{-# LANGUAGE CPP           #-}
{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE PatternGuards #-}


{-|

This module contains an optimised implementation of the reduction algorithm
from 'Agda.TypeChecking.Reduce' and 'Agda.TypeChecking.CompiledClause.Match'.
It runs roughly an order of magnitude faster than the original implementation.

The differences are the following:

- Only applies when we don't have --sharing and when all reductions are
  allowed.

  This means we can skip a number of checks that would otherwise be performed
  at each reduction step.

- Does not track whether simplifications were made.

  This information is only used when trying to simplify terms, so the
  simplifier runs the slow implementation.

- Precomputes primZero and primSuc.

  Since all the functions involved in reduction are implemented in this module
  in a single where block, we can look up zero and suc once instead of once for
  each reduction step.

- Run outside ReduceM

  ReduceM is already just a plain reader monad, but pulling out the environment
  and doing all reduction non-monadically saves a significant amount of time.

- Memoise getConstInfo.

  A big chunk of the time during reduction is spent looking up definitions in
  the signature. Any long-running reduction will use only a handful definitions
  though, so memoising getConstInfo is a big win.

- Optimised case trees.

  Since we memoise getConstInfo we can do some preprocessing of the
  definitions, returning a 'CompactDef' instead of a 'Definition'. In
  particular we streamline the case trees used for matching in a few ways:

    - Drop constructor arity information.
    - Use NameId instead of QName as map keys.
    - Special branch for natural number successor.

  None of these changes would make sense to incorporate into the actual case
  trees. The first two loses information that we need in other places and the
  third would complicate a lot of code working with case trees.

- Optimised parallel substitution.

  When substituting arguments into function bodies we always have a complete
  (a term for every free variable) parallel substitution. We run an specialised
  substitution for this case that falls back to normal substitution when it
  hits a binder.

-}
module Agda.TypeChecking.Reduce.Fast
  ( fastReduce ) where

import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Traversable (traverse)
import Data.Coerce

import System.IO.Unsafe
import Data.IORef

import Debug.Trace (trace)

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad hiding (Closure(..))
import Agda.TypeChecking.Reduce as R
import Agda.TypeChecking.Rewriting (rewrite)
import Agda.TypeChecking.Reduce.Monad as RedM
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Builtin hiding (constructorForm)
import Agda.TypeChecking.CompiledClause.Match ()

import Agda.Interaction.Options

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Memo
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

import Debug.Trace

-- Compact definitions ----------------------------------------------------

-- This is what the memoised getConstInfo returns. We essentially pick out only the
-- information needed for fast reduction from the definition.

data CompactDef =
  CompactDef { cdefDelayed        :: Bool
             , cdefNonterminating :: Bool
             , cdefDef            :: CompactDefn
             , cdefRewriteRules   :: RewriteRules
             }

data CompactDefn
  = CFun  { cfunCompiled  :: FastCompiledClauses, cfunProjection :: Maybe QName }
  | CCon  { cconSrcCon    :: ConHead }
  | CForce  -- ^ primForce
  | CTyCon  -- ^ Datatype or record type. Need to know this for primForce.
  | COther  -- ^ In this case we fall back to slow reduction

compactDef :: Maybe ConHead -> Maybe ConHead -> Maybe QName -> Definition -> RewriteRules -> ReduceM CompactDef
compactDef z s pf def rewr = do
  cdefn <-
    case theDef def of
      _ | Just (defName def) == pf -> pure CForce
      Constructor{conSrcCon = c} -> pure CCon{cconSrcCon = c}
      Function{funCompiled = Just cc, funClauses = _:_, funProjection = proj} ->
        pure CFun{ cfunCompiled   = fastCompiledClauses z s cc
                 , cfunProjection = projOrig <$> proj }
      Datatype{dataClause = Nothing} -> pure CTyCon
      Record{recClause = Nothing} -> pure CTyCon
      _ -> pure COther
  return $
    CompactDef { cdefDelayed        = defDelayed def == Delayed
               , cdefNonterminating = defNonterminating def
               , cdefDef            = cdefn
               , cdefRewriteRules   = rewr
               }

-- Faster case trees ------------------------------------------------------

data FastCase c = FBranches
  { fprojPatterns   :: Bool
    -- ^ We are constructing a record here (copatterns).
    --   'conBranches' lists projections.
  , fconBranches    :: Map NameId c
    -- ^ Map from constructor (or projection) names to their arity
    --   and the case subtree.  (Projections have arity 0.)
  , fsucBranch      :: Maybe c
  , flitBranches    :: Map Literal c
    -- ^ Map from literal to case subtree.
  , fcatchAllBranch :: Maybe c
    -- ^ (Possibly additional) catch-all clause.
  }

-- | Case tree with bodies.

data FastCompiledClauses
  = FCase Int (FastCase FastCompiledClauses)
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
    -- If the @n@-th argument is a projection, we have only 'conBranches'
    -- with arity 0.
  | FEta Int [QName] FastCompiledClauses (Maybe FastCompiledClauses)
    -- ^ Match on record constructor. Can still have a catch-all though. Just
    --   contains the fields, not the actual constructor.
  | FDone [Arg ArgName] Term
    -- ^ @Done xs b@ stands for the body @b@ where the @xs@ contains hiding
    --   and name suggestions for the free variables. This is needed to build
    --   lambdas on the right hand side for partial applications which can
    --   still reduce.
  | FFail
    -- ^ Absurd case.

-- type FastStack = [(FastCompiledClauses, [MaybeReduced (Elim' Value)], [Elim' Value] -> [Elim' Value])]

fastCompiledClauses :: Maybe ConHead -> Maybe ConHead -> CompiledClauses -> FastCompiledClauses
fastCompiledClauses z s cc =
  case cc of
    Fail              -> FFail
    Done xs b         -> FDone xs b
    Case (Arg _ n) Branches{ etaBranch = Just (c, cc), catchAllBranch = ca } ->
      FEta n (conFields c) (fastCompiledClauses z s $ content cc) (fastCompiledClauses z s <$> ca)
    Case (Arg _ n) bs -> FCase n (fastCase z s bs)

fastCase :: Maybe ConHead -> Maybe ConHead -> Case CompiledClauses -> FastCase FastCompiledClauses
fastCase z s (Branches proj con _ lit wild _) =
  FBranches
    { fprojPatterns   = proj
    , fconBranches    = Map.mapKeysMonotonic (nameId . qnameName) $ fmap (fastCompiledClauses z s . content) con
    , fsucBranch      = fmap (fastCompiledClauses z s . content) $ flip Map.lookup con . conName =<< s
    , flitBranches    = fmap (fastCompiledClauses z s) lit
    , fcatchAllBranch = fmap (fastCompiledClauses z s) wild }

{-# INLINE lookupCon #-}
lookupCon :: QName -> FastCase c -> Maybe c
lookupCon c (FBranches _ cons _ _ _) = Map.lookup (nameId $ qnameName c) cons

-- QName memo -------------------------------------------------------------

{-# NOINLINE memoQName #-}
memoQName :: (QName -> a) -> (QName -> a)
memoQName f = unsafePerformIO $ do
  tbl <- newIORef Map.empty
  return (unsafePerformIO . f' tbl)
  where
    f' tbl x = do
      let i = nameId (qnameName x)
      m <- readIORef tbl
      case Map.lookup i m of
        Just y  -> return y
        Nothing -> do
          let y = f x
          writeIORef tbl (Map.insert i y m)
          return y

-- Faster substitution ----------------------------------------------------

-- Precondition: All free variables of the term are assigned values in the
-- list.
-- Reverts to normal substitution if it hits a binder or other icky stuff (like
-- levels). It's strict in the shape of the result to avoid creating huge
-- thunks for accumulator arguments.
strictSubst :: Bool -> [Term] -> Term -> Term
strictSubst strict us
  | not strict = applySubst rho
  | otherwise  = go 0
  where
    rho = parallelS us
    go k v =
      case v of
        Var x es
          | x < k     -> Var x $! map' (goE k) es
          | otherwise -> applyE (raise k $ us !! (x - k)) $! map' (goE k) es
        Def f es -> defApp f [] $! map' (goE k) es
        Con c ci es -> Con c ci $! map' (goE k) es
        Lam i b  -> Lam i $! goAbs k b
        Lit{}    -> v
        _        -> applySubst (liftS k rho) v

    goE k (Apply v) = Apply $! mapArg' (go k) v
    goE _ p         = p

    goAbs k (Abs   x v) = Abs   x $! go (k + 1) v
    goAbs k (NoAbs x v) = NoAbs x $! go k v

map' :: (a -> b) -> [a] -> [b]
map' f []       = []
map' f (x : xs) = ((:) $! f x) $! map' f xs

mapArg' :: (a -> b) -> Arg a -> Arg b
mapArg' f (Arg i x) = Arg i $! f x


-- Fast reduction ---------------------------------------------------------

-- | First argument: allow non-terminating reductions.
fastReduce :: Bool -> Term -> ReduceM (Blocked Term)
fastReduce allowNonTerminating v = do
  let name (Con c _ _) = c
      name _         = __IMPOSSIBLE__
  z  <- fmap name <$> getBuiltin' builtinZero
  s  <- fmap name <$> getBuiltin' builtinSuc
  pf <- fmap primFunName <$> getPrimitive' "primForce"
  rwr <- optRewriting <$> pragmaOptions
  constInfo <- unKleisli $ \f -> do
    info <- getConstInfo f
    rewr <- instantiateRewriteRules =<< getRewriteRulesFor f
    compactDef z s pf info rewr
  ReduceM $ \ env -> reduceTm env (memoQName constInfo) allowNonTerminating rwr z s v

unKleisli :: (a -> ReduceM b) -> ReduceM (a -> b)
unKleisli f = ReduceM $ \ env x -> unReduceM (f x) env

-- data VSub = VSub Substitution
--           | VStrictSub [Value]

-- makeVSub :: Bool -> [MaybeReduced (Elim' Value)] -> VSub
-- makeVSub strict es
--   | strict    = VStrictSub vs
--   | otherwise = VSub sub
--   where
--     vs  = reverse $ map (unArg . argFromElim . ignoreReduced) es
--     sub = parallelS $ map valueToTerm vs

-- applyVSub :: VSub -> Value -> Value
-- applyVSub (VSub sub)      = termToValue . applySubst sub . valueToTerm
-- applyVSub (VStrictSub vs) = coerce (strictSubst True) vs

-- data ValueView = VVar {-# UNPACK #-} !Int [Elim' Value]
--                | VCon ConHead ConInfo [Elim' Value]
--                | VDef QName [Elim' Value]
--                | VLit Literal
--                | VTerm Term

-- vCon :: ConHead -> ConInfo -> [Elim' Value] -> Value
-- vCon c i es = Value (Con c i $ coerce es)

-- vDef :: QName -> [Elim' Value] -> Value
-- vDef f es = Value (Def f $ coerce es)

-- vLit :: Literal -> Value
-- vLit l = Value (Lit l)

-- valueView :: Value -> ValueView
-- valueView (Value t) =
--   case t of
--     Var x es   -> VVar x (coerce es)
--     Con c i es -> VCon c i (coerce es)
--     Def f es   -> VDef f (coerce es)
--     Lit l      -> VLit l
--     _          -> VTerm t

-- valueToTerm :: Value -> Term
-- valueToTerm = coerce

-- elimsToTerm :: [Elim' Value] -> Elims
-- elimsToTerm = coerce

-- termToValue :: Term -> Value
-- termToValue = coerce

-- closure :: VSub -> Term -> Value
-- closure sub t = applyVSub sub (termToValue t)

-- applyV :: Value -> [Elim' Value] -> Value
-- applyV = coerce (applyE :: Term -> Elims -> Term)

-- | For some reason...
topMetaIsNotBlocked :: Blocked Term -> Blocked Term
topMetaIsNotBlocked (Blocked _ t@MetaV{}) = notBlocked t
topMetaIsNotBlocked b = b

data Closure = Closure Term Env Stack  -- Env applied to the Term (the stack contains closures)
type Env = [Closure]

lookupEnv :: Int -> Env -> Maybe Closure
lookupEnv i e | length e < i = Nothing
              | otherwise    = Just (e !! i)

type Stack = [Elim' Closure]

clApply :: Closure -> Stack -> Closure
clApply (Closure t env es) es' = Closure t env (es ++ es')

type ControlStack = [ControlFrame]
data ControlFrame = DoCase QName ArgInfo Closure (FastCase FastCompiledClauses) (Stack -> Stack) Stack Stack

data Focus = Eval Closure
           | Match QName Closure FastCompiledClauses (Stack -> Stack) Stack
           | Value (Blocked Closure)

type AM = (Focus, ControlStack)

instance Pretty Closure where
  prettyPrec p (Closure t env stack) =
    mparens (p > 9) $ fsep [ text "Closure"
                           , nest 2 $ prettyPrec 10 t
                           , nest 2 $ prettyList env
                           , nest 2 $ prettyList stack ]

instance Pretty Focus where
  prettyPrec p (Eval cl)  = mparens (p > 9) (text "Eval" <?> prettyPrec 10 cl)
  prettyPrec p (Value cl) = mparens (p > 9) (text "Value" <?> prettyPrec 10 (ignoreBlocking cl))
  prettyPrec p (Match _ cl _ _ st) = mparens (p > 9) (text "Match" <?> prettyPrec 10 (clApply cl st))

instance Pretty ControlFrame where
  pretty (DoCase{}) = text "DoCase{}"

compile :: Term -> AM
compile t = (Eval (Closure t [] []), [])

decodeClosure :: Closure -> Term
decodeClosure (Closure t [] st) = t `applyE` (map . fmap) decodeClosure st
decodeClosure (Closure t e st)  = decodeClosure (Closure (applySubst (parallelS $ map decodeClosure e) t) [] st)

decode :: AM -> Blocked Term
decode (Value c, []) = topMetaIsNotBlocked $ fmap decodeClosure c
decode (Value arg, DoCase _ i cl _ patch stack0 stack1 : ctrl) =
  -- TODO: check this
  decode (Value (clApply cl stack <$ arg), ctrl)
  where stack = patch $ stack0 ++ [Apply . Arg i $ ignoreBlocking arg] ++ stack1
decode (Eval c, ctrl) = decode (Value $ notBlocked c, ctrl)   -- only for fallback to slow reduce(?)
decode (Match{}, ctrl) = __IMPOSSIBLE__

elimsToStack :: Env -> Elims -> Stack
elimsToStack env = (map . fmap) (mkClosure env)
  where mkClosure env t = Closure t env []

reduceTm :: ReduceEnv -> (QName -> CompactDef) -> Bool -> Bool -> Maybe ConHead -> Maybe ConHead -> Term -> Blocked Term
reduceTm env !constInfo allowNonTerminating hasRewriting zero suc = decode . runAM . compile
    -- fmap valueToTerm . reduceB' 0 . termToValue
  where
    -- Force substitutions every nth step to avoid memory leaks. Doing it in
    -- every is too expensive (issue 2215).
    -- strictEveryNth = 1000

    runReduce m = unReduceM m env
    conNameId = nameId . qnameName . conName
    isZero =
      case zero of
        Nothing -> const False
        Just z  -> (conNameId z ==) . conNameId

    isSuc  =
      case suc of
        Nothing -> const False
        Just s  -> (conNameId s ==) . conNameId

    runAM s = runAM' s -- trace (prettyShow s) (runAM' s)

    runAM' :: AM -> AM
    runAM' s@(Value{}, []) = s
    runAM' s@(Eval cl@(Closure t env stack), ctrl) =
      case t of

        Def f [] ->
          case cdefDef (constInfo f) of
            CFun{ cfunCompiled = cc } -> runAM (Match f (Closure t [] []) cc id stack, ctrl)
            CTyCon                    -> runAM done
            CCon{}                    -> __IMPOSSIBLE__
            CForce                    -> __IMPOSSIBLE__ -- TODO
            COther                    -> __IMPOSSIBLE__ -- TODO
        Con c i [] -> runAM (Value (notBlocked $ Closure (Con c' i []) env stack), ctrl)
          where CCon{cconSrcCon = c'} = cdefDef (constInfo (conName c))
          -- TODO: numbers
          -- TODO: projection

        Var x []   ->
          case lookupEnv x env of
            Nothing -> runAM done
            Just cl -> runAM (Eval (clApply cl stack), ctrl)

        MetaV m [] -> runAM (Value (blocked m cl), ctrl)

        Lit{} -> runAM done
        Pi{}  -> runAM done

        Lam h (Abs _ b)
          | Apply v : stack' <- stack -> runAM (evalClosure b (unArg v : env) stack', ctrl)
        Lam h (NoAbs _ b)
          | _ : stack' <- stack -> runAM (evalClosure b env stack', ctrl)

        Def f es   -> runAM (evalClosure (Def f [])   env $ elimsToStack env es ++ stack, ctrl)
        Con c i es -> runAM (evalClosure (Con c i []) env $ elimsToStack env es ++ stack, ctrl)
        Var x es   -> runAM (evalClosure (Var x [])   env $ elimsToStack env es ++ stack, ctrl)
        MetaV m es -> runAM (evalClosure (MetaV m []) env $ elimsToStack env es ++ stack, ctrl)

        _ -> fallback s
      where done = (Value (notBlocked cl), ctrl)

    -- Pattern matching against a value
    runAM' s@(Value bv, DoCase f i cl0 bs patch stack0 stack1 : ctrl) =
      case bv of
        Blocked{} -> runAM stuck
        NotBlocked _ cl@(Closure t env stack) -> case t of
          Con c ci [] ->
            (lookupCon (conName c) bs =>? \ cc ->
                -- Matching constructor
                runAM (Match f cl0 cc (patch . patchCon) (stack0 ++ stack ++ stack1), ctrl)) $
            (fcatchAllBranch bs =>? \ cc ->
                -- No matching case, check catch-all
                runAM (Match f cl0 cc (patch . patchWild) (stack0 ++ stack1), ctrl)) $
            runAM stuck   -- no catch-all, TODO: fall-through to parent catch-alls, or transform case tree?
            where
              -- TODO: this is terrible
              n  = length stack0
              ar = length stack
              patchCon es = es0 ++ [Apply $ Arg i $ Closure (Con c ci []) [] es1] ++ es2
                where (es0, rest) = splitAt n es
                      (es1, es2)  = splitAt ar rest
          Con{} -> __IMPOSSIBLE__ -- elims should have been shifted onto the stack
          Lit{} -> __IMPOSSIBLE__ -- TODO
          _ -> runAM stuck -- TODO
      where
        cl = ignoreBlocking bv
        patchWild es = es0 ++ [Apply $ Arg i cl] ++ es1
          where (es0, es1) = splitAt (length stack0) es
        stuck = (Value (clApply cl0 stack' <$ bv), ctrl)
          where stack' = stack0 ++ [Apply $ Arg i cl] ++ stack1

    runAM' s@(Match f cl0 cc patch stack, ctrl) =
      case cc of
        -- impossible case
        FFail         -> runAM (Value $ NotBlocked AbsurdMatch $ cl0 `clApply` patch stack, ctrl)
        FDone xs body -> runAM (Eval (Closure (lams zs body) env stack'), ctrl)
          where
            -- Build the environment for the body from the top of the stack. Also returns
            -- the remaining stack and names for missing arguments in case of
            -- partial application.
            buildEnv xs [] env = (xs, env, [])
            buildEnv [] st env = ([], env, st)
            buildEnv (x : xs) (Apply c : st) env = buildEnv xs st (unArg c : env)
            buildEnv (_ : _) (_ : _) _ = __IMPOSSIBLE__

            (zs, env, stack') = buildEnv xs stack []

            lams xs t = foldr lam t xs
            lam x t = Lam (argInfo x) (Abs (unArg x) t)

        -- Split on nth elimination on the stac
        FCase n bs ->
          case splitAt n stack of
            -- If the nth elimination is not given, we're done
            (_, []) -> runAM (done Underapplied)
            -- apply elim: push the current match on the control stack and
            -- evaluate the argument
            (stack0, Apply e : stack1) -> runAM (Eval (unArg e), DoCase f (argInfo e) cl0 bs patch stack0 stack1 : ctrl)
            -- projection elim
            (stack0, e@(Proj o p) : stack1) ->
              case lookupCon p bs of
                Nothing -> runAM (done $ StuckOn (Proj o p)) -- No case for the projection: stop
                Just cc -> runAM (Match f cl0 cc (patch . patchProj) (stack0 ++ stack1), ctrl)
              where patchProj st = st0 ++ [e] ++ st1
                      where (st0, st1) = splitAt n st
      where done why = (Value $ NotBlocked why $ cl0 `clApply` patch stack, ctrl)

    evalClosure = ((Eval .) .) . Closure

    (=>?) :: Maybe a -> (a -> b) -> b -> b
    (m =>? f) z = maybe z f m

    fallback :: AM -> AM
    fallback = mkValue . runReduce . slowReduceTerm . ignoreBlocking . decode
      where mkValue b = (Value (b <&> \ t -> Closure t [] []), [])

    -- reduceB' :: Int -> Value -> Blocked Value
    -- reduceB' steps v =
    --   case valueView v of
    --     VDef f es -> unfoldDefinitionE steps False reduceB' (vDef f []) f es
    --     VCon c ci vs ->
    --       -- Constructors can reduce' when they come from an
    --       -- instantiated module.
    --       case unfoldDefinitionE steps False reduceB' (vCon c ci []) (conName c) vs of
    --         NotBlocked r v -> NotBlocked r $ reduceNat v
    --         b              -> b
    --     VLit{} -> notBlocked v
    --     VVar{} -> notBlocked v
    --     _      -> fmap termToValue $ runReduce (slowReduceTerm $ valueToTerm v)
    --   where
    --     reduceNat :: Value -> Value
    --     reduceNat v =
    --       case valueView v of
    --         VCon c ci []        | isZero c -> vLit (LitNat (getRange c) 0)
    --         VCon c ci [Apply a] | isSuc c  -> inc . ignoreBlocking $ reduceB' 0 (unArg a)
    --           where
    --             inc w | VLit (LitNat r n) <- valueView w = vLit (LitNat noRange $ n + 1)
    --             inc w = vCon c ci [Apply $ defaultArg w]
    --         _                              -> v

    -- originalProjection :: QName -> QName
    -- originalProjection q =
    --   case cdefDef $ constInfo q of
    --     CFun{ cfunProjection = Just p } -> p
    --     _                               -> __IMPOSSIBLE__

    -- -- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
    -- -- need also to instantiate metas, see Issue 826.
    -- unfoldCorecursionE :: Elim' Value -> Blocked (Elim' Value)
    -- unfoldCorecursionE (Proj o p)           = notBlocked $ Proj o $ originalProjection p
    -- unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) $
    --   unfoldCorecursion 0 v

    -- unfoldCorecursion :: Int -> Value -> Blocked Value
    -- unfoldCorecursion steps v =
    --   case valueView v of
    --     VDef f es -> unfoldDefinitionE steps True unfoldCorecursion (vDef f []) f es
    --     _         -> reduceB' steps v

    -- unfoldDefinitionE ::
    --   Int -> Bool -> (Int -> Value -> Blocked Value) ->
    --   Value -> QName -> [Elim' Value] -> Blocked Value
    -- unfoldDefinitionE steps unfoldDelayed keepGoing v f es =
    --   case unfoldDefinitionStep steps unfoldDelayed (constInfo f) v f es of
    --     NoReduction v    -> v
    --     YesReduction _ v -> (keepGoing $! steps + 1) v

    -- reducedToValue (YesReduction r v) = YesReduction r (termToValue v)
    -- reducedToValue (NoReduction b)    = NoReduction (fmap termToValue b)

    -- rewriteValue b v0 rewr es =
    --   reducedToValue $ runReduce $ rewrite b (valueToTerm v0) rewr $ elimsToTerm es

    -- unfoldDefinitionStep :: Int -> Bool -> CompactDef -> Value -> QName -> [Elim' Value] -> Reduced (Blocked Value) Value
    -- unfoldDefinitionStep steps unfoldDelayed CompactDef{cdefDelayed = delayed, cdefNonterminating = nonterm, cdefDef = def, cdefRewriteRules = rewr} v0 f es =
    --       -- Non-terminating functions
    --       -- (i.e., those that failed the termination check)
    --       -- and delayed definitions
    --       -- are not unfolded unless explicitely permitted.
    --   let dontUnfold =
    --            (not allowNonTerminating && nonterm)
    --         || (not unfoldDelayed       && delayed)
    --   in case def of
    --     CCon{cconSrcCon = c}
    --       | hasRewriting -> rewriteValue (notBlocked ()) (vCon c ConOSystem []) rewr es
    --       | otherwise    -> NoReduction $ notBlocked $ vCon c ConOSystem [] `applyV` es
    --     CFun{cfunCompiled = cc} -> reduceNormalE steps v0 f (map notReduced es) dontUnfold cc
    --     CForce -> reduceForce unfoldDelayed v0 f es
    --     CTyCon | hasRewriting -> rewriteValue (notBlocked ()) v0 rewr es
    --            | otherwise    -> NoReduction $ notBlocked (v0 `applyV` es)
    --     COther -> reducedToValue $ runReduce $ R.unfoldDefinitionStep unfoldDelayed (valueToTerm v0) f $ elimsToTerm es
    --   where
    --     yesReduction = YesReduction NoSimplification

    --     reduceForce :: Bool -> Value -> QName -> [Elim' Value] -> Reduced (Blocked Value) Value
    --     reduceForce unfoldDelayed v0 pf (Apply a : Apply b : Apply s : Apply t : Apply u : Apply f : es) =
    --       case reduceB' 0 (unArg u) of
    --         ub@Blocked{}        -> noGo ub
    --         ub@(NotBlocked _ u)
    --           | isWHNF u  -> yesReduction $ unArg f `applyV` (Apply (defaultArg u) : es)
    --           | otherwise -> noGo ub
    --       where
    --         noGo ub = NoReduction $ ub <&> \ u -> vDef pf (Apply a : Apply b : Apply s : Apply t : Apply (defaultArg u) : Apply f : es)

    --         isWHNF u = case valueToTerm u of
    --             Lit{}      -> True
    --             Con{}      -> True
    --             Lam{}      -> True
    --             Pi{}       -> True
    --             Sort{}     -> True
    --             Level{}    -> True
    --             DontCare{} -> True
    --             MetaV{}    -> False
    --             Var{}      -> False
    --             Def q _    -> isTyCon q
    --             Shared{}   -> __IMPOSSIBLE__

    --         isTyCon q =
    --           case cdefDef $ constInfo q of
    --             CTyCon -> True
    --             _      -> False

    --     -- TODO: partially applied to u
    --     reduceForce unfoldDelayed v0 pf es = reducedToValue $ runReduce $ R.unfoldDefinitionStep unfoldDelayed (valueToTerm v0) f (elimsToTerm es)

    --     reduceNormalE :: Int -> Value -> QName -> [MaybeReduced (Elim' Value)] -> Bool -> FastCompiledClauses -> Reduced (Blocked Value) Value
    --     reduceNormalE steps v0 f es dontUnfold cc
    --       | dontUnfold = defaultResult  -- non-terminating or delayed
    --       | otherwise  =
    --         case match' steps f [(cc, es, id)] of
    --           YesReduction s u -> YesReduction s u
    --           NoReduction es' | hasRewriting -> rewriteValue (void es') v0 rewr (ignoreBlocking es')
    --                           | otherwise    -> NoReduction $ applyV v0 <$> es'
    --       where defaultResult | hasRewriting = rewriteValue (NotBlocked ReallyNotBlocked ()) v0 rewr (map ignoreReduced es)
    --                           | otherwise    = NoReduction $ NotBlocked ReallyNotBlocked vfull
    --             vfull = v0 `applyV` map ignoreReduced es

    --     match' :: Int -> QName -> FastStack -> Reduced (Blocked [Elim' Value]) Value
    --     match' steps f ((c, es, patch) : stack) =
    --       let no blocking es = NoReduction $ blocking $ patch $ map ignoreReduced es
    --           yes t          = yesReduction t

    --       in case c of

    --         -- impossible case
    --         FFail -> no (NotBlocked AbsurdMatch) es

    --         -- done matching
    --         FDone xs t
    --           -- common case: exact number of arguments
    --           | m == n    -> {-# SCC match'Done #-} yes $ doSubst es t
    --           -- if the function was partially applied, return a lambda
    --           | m < n     -> yes $ doSubst es $ foldr lam t (drop m xs)
    --           -- otherwise, just apply instantiation to body
    --           -- apply the result to any extra arguments
    --           | otherwise -> yes $ doSubst es0 t `applyV` map ignoreReduced es1
    --           where
    --             n = length xs
    --             m = length es
    --             useStrictSubst = rem steps strictEveryNth == 0
    --             doSubst es t = closure sub t
    --               where sub = makeVSub useStrictSubst es
    --             -- doSubst es t = strictSubst useStrictSubst (reverse $ map (unArg . argFromElim . ignoreReduced) es) t
    --             (es0, es1) = splitAt n es
    --             lam x t    = Lam (argInfo x) (Abs (unArg x) t)

    --         -- splitting on the @n@th elimination
    --         FCase n bs -> {-# SCC "match'Case" #-}
    --           case splitAt n es of
    --             -- if the @n@th elimination is not supplied, no match
    --             (_, []) -> no (NotBlocked Underapplied) es
    --             -- if the @n@th elimination is @e0@
    --             (es0, MaybeRed red e0 : es1) ->
    --               -- get the reduced form of @e0@
    --               let eb = case red of
    --                          Reduced b  -> e0 <$ b
    --                          NotReduced -> unfoldCorecursionE e0
    --                   e = ignoreBlocking eb
    --                   -- replace the @n@th argument by its reduced form
    --                   es' = es0 ++ [MaybeRed (Reduced $ () <$ eb) e] ++ es1
    --                   -- if a catch-all clause exists, put it on the stack
    --                   catchAllFrame stack = maybe stack (\c -> (c, es', patch) : stack) (fcatchAllBranch bs)
    --                   -- If our argument is @Lit l@, we push @litFrame l@ onto the stack.
    --                   litFrame l stack =
    --                     case Map.lookup l (flitBranches bs) of
    --                       Nothing -> stack
    --                       Just cc -> (cc, es0 ++ es1, patchLit) : stack
    --                   -- If our argument (or its constructor form) is @Con c ci vs@
    --                   -- we push @conFrame c ci vs@ onto the stack.
    --                   conFrame c ci vs stack =
    --                     case lookupCon (conName c) bs of
    --                       Nothing -> stack
    --                       Just cc -> ( cc
    --                                  , es0 ++ map (MaybeRed NotReduced) vs ++ es1
    --                                  , patchCon c ci (length vs)
    --                                  ) : stack

    --                   sucFrame n stack =
    --                     case fsucBranch bs of
    --                       Nothing -> stack
    --                       Just cc -> (cc, es0 ++ [v] ++ es1, patchCon (fromJust suc) ConOSystem 1)
    --                                  : stack
    --                     where v = MaybeRed (Reduced $ notBlocked ()) $ Apply $ defaultArg $ vLit $ LitNat noRange n

    --                   -- If our argument is @Proj p@, we push @projFrame p@ onto the stack.
    --                   projFrame p stack =
    --                     case lookupCon p bs of
    --                       Nothing -> stack
    --                       Just cc -> (cc, es0 ++ es1, patchLit) : stack
    --                   -- The new patch function restores the @n@th argument to @v@:
    --                   -- In case we matched a literal, just put @v@ back.
    --                   patchLit es = patch (es0 ++ [e] ++ es1)
    --                     where (es0, es1) = splitAt n es
    --                   -- In case we matched constructor @c@ with @m@ arguments,
    --                   -- contract these @m@ arguments @vs@ to @Con c ci vs@.
    --                   patchCon c ci m es = patch (es0 ++ [vCon c ci vs <$ e] ++ es2)
    --                     where (es0, rest) = splitAt n es
    --                           (es1, es2)  = splitAt m rest
    --                           vs          = es1
    --               -- Now do the matching on the @n@ths argument:
    --               in case eb of
    --                 Blocked x _       -> no (Blocked x) es'
    --                 NotBlocked blk elim ->
    --                   case elim of
    --                     Apply (Arg info v) ->
    --                       case valueView v of
    --                         VTerm (MetaV x _) -> no (Blocked x) es'

    --                         -- In case of a natural number literal, try also its constructor form
    --                         VLit l@(LitNat r n) ->
    --                           let cFrame stack
    --                                 | n > 0                  = sucFrame (n - 1) stack
    --                                 | n == 0, Just z <- zero = conFrame z ConOSystem [] stack
    --                                 | otherwise              = stack
    --                           in match' steps f $ litFrame l $ cFrame $ catchAllFrame stack

    --                         VLit l    -> match' steps f $ litFrame l    $ catchAllFrame stack
    --                         VCon c ci vs -> match' steps f $ conFrame c ci vs $ catchAllFrame $ stack

    --                         -- Otherwise, we are stuck.  If we were stuck before,
    --                         -- we keep the old reason, otherwise we give reason StuckOn here.
    --                         _ -> no (NotBlocked $ stuckOn (fmap valueToTerm elim) blk) es'

    --                     -- In case of a projection, push the projFrame
    --                     Proj _ p -> match' steps f $ projFrame p stack


    --     -- If we reach the empty stack, then pattern matching was incomplete
    --     match' _ f [] = runReduce $ do
    --       pds <- getPartialDefs
    --       if f `elem` pds
    --       then return (NoReduction $ NotBlocked MissingClauses es)
    --       else do
    --         traceSLn "impossible" 10
    --           ("Incomplete pattern matching when applying " ++ show f)
    --           __IMPOSSIBLE__
