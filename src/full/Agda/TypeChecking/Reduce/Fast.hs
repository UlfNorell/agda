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

import System.IO.Unsafe
import Data.IORef

import Debug.Trace (trace)

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce as R
import Agda.TypeChecking.Rewriting (rewrite)
import Agda.TypeChecking.Reduce.Monad as RedM
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Builtin hiding (constructorForm)
import Agda.TypeChecking.CompiledClause.Match

import Agda.Interaction.Options

import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Memo
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Pretty (prettyShow)

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

type FastStack = [(FastCompiledClauses, [MaybeReduced (Elim' Value)], [Elim' Value] -> [Elim' Value])]

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

data VSub = VSub [Value] Substitution

vSubToSub :: VSub -> Substitution
vSubToSub (VSub _ sub) = sub

makeVSub :: [MaybeReduced (Elim' Value)] -> VSub
makeVSub es = VSub vs sub
  where
    vs  = reverse $ map (unArg . argFromElim . ignoreReduced) es
    sub = parallelS $ map valueToTerm vs

lookupVSub :: VSub -> Int -> Value
lookupVSub (VSub vs _) i = vs !! i

-- Not quite value..
data Value = VCon ConHead ConInfo [Elim' Value]
           | VVar {-# UNPACK #-} !Int [Elim' Value]
           | VDef QName [Elim' Value]
           | VLit Literal
           | VClosure VSub Term [Elim' Value] -- ?

showValue :: Value -> String
showValue v = case v of
  VCon h _ _     -> "VCon " ++ show h
  VDef f _       -> "VDef " ++ show f
  VLit l         -> "VLit " ++ show l
  VVar i _       -> "VVar " ++ show i
  VClosure _ _ _ -> "VClosure{}"

valueToTerm :: Value -> Term
valueToTerm (VCon c i es)    = Con c i $ elimsToTerm es
valueToTerm (VDef f es)      = Def f   $ elimsToTerm es
valueToTerm (VVar x es)      = Var x   $ elimsToTerm es
valueToTerm (VLit l)         = Lit l
valueToTerm (VClosure sub v es) = applySubst (vSubToSub sub) v `applyE` elimsToTerm es

elimsToTerm :: [Elim' Value] -> Elims
elimsToTerm = (map . fmap) valueToTerm

termToValue :: Term -> Value
termToValue (Con c h es) = VCon c h $ (map . fmap) termToValue es
termToValue (Def f es)   = VDef f $ (map . fmap) termToValue es
termToValue (Var i es)   = VVar i $ (map . fmap) termToValue es
termToValue (Lit l)      = VLit l
termToValue v            = VClosure (makeVSub []) v []  -- !! Not correct for open terms !!

closure :: VSub -> Term -> Value
closure sub t = VClosure sub t []

pushSubst :: Value -> Value
pushSubst (VClosure sub t es) = (`applyV` es) $
  case t of
    Con c h es -> VCon c h $ closE es
    Def f es   -> VDef f   $ closE es
    Lit l      -> VLit l
    Var i es   -> pushSubst $ lookupVSub sub i `applyV` closE es
    _          -> closure sub t
  where closE = (map . fmap) (closure sub)
pushSubst v = v

applyV :: Value -> [Elim' Value] -> Value
applyV v []  = v
applyV v es' = case v of
  VCon c h es       -> conAppV c h es es'
  VDef f es         -> defAppV f es es'
  VVar x es         -> VVar x   $ es ++ es'
  VLit l            -> __IMPOSSIBLE__
  VClosure sub u es -> VClosure sub u $ es ++ es'

canProjectV :: QName -> Value -> Maybe (Arg Value)
canProjectV f v =
  case v of
    VCon (ConHead _ _ fs) _ vs -> do
      i <- List.elemIndex f fs
      isApplyElim =<< headMaybe (drop i vs)
    _ -> Nothing

conAppV :: ConHead -> ConInfo -> [Elim' Value] -> [Elim' Value] -> Value
conAppV ch                  ci args []               = VCon ch ci args
conAppV ch                  ci args (a@Apply{} : es) = conAppV ch ci (args ++ [a]) es --- !!!
conAppV ch@(ConHead c _ fs) ci args (Proj o f : es)  = applyV v es
  where
    isApply e = fromMaybe __IMPOSSIBLE__ $ isApplyElim e
    i = maybe __IMPOSSIBLE__ id $ List.elemIndex f fs
    v = maybe __IMPOSSIBLE__ (argToDontCareV . isApply)  $ headMaybe $ drop i args

defAppV :: QName -> [Elim' Value] -> [Elim' Value] -> Value
defAppV f [] (Apply a : es) | Just v <- canProjectV f (unArg a)
  = argToDontCareV v `applyV` es
defAppV f es0 es = VDef f $ es0 ++ es

argToDontCareV :: Arg Value -> Value
argToDontCareV (Arg ai v)
  | Irrelevant <- getRelevance ai = closure (makeVSub []) (dontCare $ valueToTerm v)
  | otherwise                     = v

reduceTm :: ReduceEnv -> (QName -> CompactDef) -> Bool -> Bool -> Maybe ConHead -> Maybe ConHead -> Term -> Blocked Term
reduceTm env !constInfo allowNonTerminating hasRewriting zero suc = fmap valueToTerm . reduceB' 0 . termToValue
  where
    -- Force substitutions every nth step to avoid memory leaks. Doing it in
    -- every is too expensive (issue 2215).
    strictEveryNth = 1000

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

    reduceB' :: Int -> Value -> Blocked Value
    reduceB' steps v =
      case pushSubst v of
        VDef f es -> unfoldDefinitionE steps False reduceB' (VDef f []) f es
        VCon c ci vs ->
          -- Constructors can reduce' when they come from an
          -- instantiated module.
          case unfoldDefinitionE steps False reduceB' (VCon c ci []) (conName c) vs of
            NotBlocked r v -> NotBlocked r $ reduceNat v
            b              -> b
        VLit{} -> notBlocked v
        VVar{} -> notBlocked v
        v      -> fmap termToValue $ runReduce (slowReduceTerm $ valueToTerm v)
      where
        reduceNat :: Value -> Value
        reduceNat v@(VCon c ci [])
          | isZero c = VLit $ LitNat (getRange c) 0
        reduceNat v@(VCon c ci [Apply a])
          | isSuc c  = inc . ignoreBlocking $ reduceB' 0 (unArg a)
          where
            inc (VLit (LitNat r n)) = VLit (LitNat noRange $ n + 1)
            inc w                   = VCon c ci [Apply $ defaultArg w]
        reduceNat v = v

    originalProjection :: QName -> QName
    originalProjection q =
      case cdefDef $ constInfo q of
        CFun{ cfunProjection = Just p } -> p
        _                               -> __IMPOSSIBLE__

    -- Andreas, 2013-03-20 recursive invokations of unfoldCorecursion
    -- need also to instantiate metas, see Issue 826.
    unfoldCorecursionE :: Elim' Value -> Blocked (Elim' Value)
    unfoldCorecursionE (Proj o p)           = notBlocked $ Proj o $ originalProjection p
    unfoldCorecursionE (Apply (Arg info v)) = fmap (Apply . Arg info) $
      unfoldCorecursion 0 v

    unfoldCorecursion :: Int -> Value -> Blocked Value
    unfoldCorecursion steps (VDef f es) = unfoldDefinitionE steps True unfoldCorecursion (VDef f []) f es
    unfoldCorecursion steps v          = reduceB' steps v

    unfoldDefinitionE ::
      Int -> Bool -> (Int -> Value -> Blocked Value) ->
      Value -> QName -> [Elim' Value] -> Blocked Value
    unfoldDefinitionE steps unfoldDelayed keepGoing v f es =
      case unfoldDefinitionStep steps unfoldDelayed (constInfo f) v f es of
        NoReduction v    -> v
        YesReduction _ v -> (keepGoing $! steps + 1) v

    reducedToValue (YesReduction r v) = YesReduction r (termToValue v)
    reducedToValue (NoReduction b)    = NoReduction (fmap termToValue b)

    rewriteValue b v0 rewr es =
      reducedToValue $ runReduce $ rewrite b (valueToTerm v0) rewr $ elimsToTerm es

    unfoldDefinitionStep :: Int -> Bool -> CompactDef -> Value -> QName -> [Elim' Value] -> Reduced (Blocked Value) Value
    unfoldDefinitionStep steps unfoldDelayed CompactDef{cdefDelayed = delayed, cdefNonterminating = nonterm, cdefDef = def, cdefRewriteRules = rewr} v0 f es =
          -- Non-terminating functions
          -- (i.e., those that failed the termination check)
          -- and delayed definitions
          -- are not unfolded unless explicitely permitted.
      let dontUnfold =
               (not allowNonTerminating && nonterm)
            || (not unfoldDelayed       && delayed)
      in case def of
        CCon{cconSrcCon = c}
          | hasRewriting -> rewriteValue (notBlocked ()) (VCon c ConOSystem []) rewr es
          | otherwise    -> NoReduction $ notBlocked $ VCon c ConOSystem [] `applyV` es
        CFun{cfunCompiled = cc} -> reduceNormalE steps v0 f (map notReduced es) dontUnfold cc
        CForce -> reduceForce unfoldDelayed v0 f es
        CTyCon | hasRewriting -> rewriteValue (notBlocked ()) v0 rewr es
               | otherwise    -> NoReduction $ notBlocked (v0 `applyV` es)
        COther -> reducedToValue $ runReduce $ R.unfoldDefinitionStep unfoldDelayed (valueToTerm v0) f $ elimsToTerm es
      where
        yesReduction = YesReduction NoSimplification

        reduceForce :: Bool -> Value -> QName -> [Elim' Value] -> Reduced (Blocked Value) Value
        reduceForce unfoldDelayed v0 pf (Apply a : Apply b : Apply s : Apply t : Apply u : Apply f : es) =
          case reduceB' 0 (unArg u) of
            ub@Blocked{}        -> noGo ub
            ub@(NotBlocked _ u)
              | isWHNF u  -> yesReduction $ unArg f `applyV` (Apply (defaultArg u) : es)
              | otherwise -> noGo ub
          where
            noGo ub = NoReduction $ ub <&> \ u -> VDef pf (Apply a : Apply b : Apply s : Apply t : Apply (defaultArg u) : Apply f : es)

            isWHNF u = case valueToTerm u of
                Lit{}      -> True
                Con{}      -> True
                Lam{}      -> True
                Pi{}       -> True
                Sort{}     -> True
                Level{}    -> True
                DontCare{} -> True
                MetaV{}    -> False
                Var{}      -> False
                Def q _    -> isTyCon q
                Shared{}   -> __IMPOSSIBLE__

            isTyCon q =
              case cdefDef $ constInfo q of
                CTyCon -> True
                _      -> False

        -- TODO: partially applied to u
        reduceForce unfoldDelayed v0 pf es = reducedToValue $ runReduce $ R.unfoldDefinitionStep unfoldDelayed (valueToTerm v0) f (elimsToTerm es)

        reduceNormalE :: Int -> Value -> QName -> [MaybeReduced (Elim' Value)] -> Bool -> FastCompiledClauses -> Reduced (Blocked Value) Value
        reduceNormalE steps v0 f es dontUnfold cc
          | dontUnfold = defaultResult  -- non-terminating or delayed
          | otherwise  =
            case match' steps f [(cc, es, id)] of
              YesReduction s u -> YesReduction s u
              NoReduction es' | hasRewriting -> rewriteValue (void es') v0 rewr (ignoreBlocking es')
                              | otherwise    -> NoReduction $ applyV v0 <$> es'
          where defaultResult | hasRewriting = rewriteValue (NotBlocked ReallyNotBlocked ()) v0 rewr (map ignoreReduced es)
                              | otherwise    = NoReduction $ NotBlocked ReallyNotBlocked vfull
                vfull = v0 `applyV` map ignoreReduced es

        match' :: Int -> QName -> FastStack -> Reduced (Blocked [Elim' Value]) Value
        match' steps f ((c, es, patch) : stack) =
          let no blocking es = NoReduction $ blocking $ patch $ map ignoreReduced es
              yes t          = yesReduction t

          in case c of

            -- impossible case
            FFail -> no (NotBlocked AbsurdMatch) es

            -- done matching
            FDone xs t
              -- common case: exact number of arguments
              | m == n    -> {-# SCC match'Done #-} yes $ doSubst es t
              -- if the function was partially applied, return a lambda
              | m < n     -> yes $ doSubst es $ foldr lam t (drop m xs)
              -- otherwise, just apply instantiation to body
              -- apply the result to any extra arguments
              | otherwise -> yes $ doSubst es0 t `applyV` map ignoreReduced es1
              where
                n = length xs
                m = length es
                useStrictSubst = rem steps strictEveryNth == 0
                doSubst es t = closure sub t
                  where sub = makeVSub es
                -- doSubst es t = strictSubst useStrictSubst (reverse $ map (unArg . argFromElim . ignoreReduced) es) t
                (es0, es1) = splitAt n es
                lam x t    = Lam (argInfo x) (Abs (unArg x) t)

            -- matching on an eta-record constructor
            FEta n fs cc ca ->
              case splitAt n es of
                (_, []) -> no (NotBlocked Underapplied) es
                (es0, MaybeRed _ e@(Apply (Arg _ v0)) : es1) ->
                    let projs = [ MaybeRed NotReduced $ Apply $ defaultArg $ v0 `applyE` [Proj ProjSystem f] | f <- fs ]
                        catchAllFrame stack = maybe stack (\c -> (c, es, patch) : stack) ca in
                    match' steps f $ (cc, es0 ++ projs ++ es1, patchEta) : catchAllFrame stack
                  where
                    patchEta es = patch (es0 ++ [e] ++ es1)
                      where (es0, es') = splitAt n es
                            (_, es1)   = splitAt (length fs) es'
                _ -> __IMPOSSIBLE__

            -- splitting on the @n@th elimination
            FCase n bs -> {-# SCC "match'Case" #-}
              case splitAt n es of
                -- if the @n@th elimination is not supplied, no match
                (_, []) -> no (NotBlocked Underapplied) es
                -- if the @n@th elimination is @e0@
                (es0, MaybeRed red e0 : es1) ->
                  -- get the reduced form of @e0@
                  let eb = case red of
                             Reduced b  -> e0 <$ b
                             NotReduced -> unfoldCorecursionE e0
                      e = ignoreBlocking eb
                      -- replace the @n@th argument by its reduced form
                      es' = es0 ++ [MaybeRed (Reduced $ () <$ eb) e] ++ es1
                      -- if a catch-all clause exists, put it on the stack
                      catchAllFrame stack = maybe stack (\c -> (c, es', patch) : stack) (fcatchAllBranch bs)
                      -- If our argument is @Lit l@, we push @litFrame l@ onto the stack.
                      litFrame l stack =
                        case Map.lookup l (flitBranches bs) of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ es1, patchLit) : stack
                      -- If our argument (or its constructor form) is @Con c ci vs@
                      -- we push @conFrame c ci vs@ onto the stack.
                      conFrame c ci vs stack =
                        case lookupCon (conName c) bs of
                          Nothing -> stack
                          Just cc -> ( cc
                                     , es0 ++ map (MaybeRed NotReduced) vs ++ es1
                                     , patchCon c ci (length vs)
                                     ) : stack

                      sucFrame n stack =
                        case fsucBranch bs of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ [v] ++ es1, patchCon (fromJust suc) ConOSystem 1)
                                     : stack
                        where v = MaybeRed (Reduced $ notBlocked ()) $ Apply $ defaultArg $ VLit $ LitNat noRange n

                      -- If our argument is @Proj p@, we push @projFrame p@ onto the stack.
                      projFrame p stack =
                        case lookupCon p bs of
                          Nothing -> stack
                          Just cc -> (cc, es0 ++ es1, patchLit) : stack
                      -- The new patch function restores the @n@th argument to @v@:
                      -- In case we matched a literal, just put @v@ back.
                      patchLit es = patch (es0 ++ [e] ++ es1)
                        where (es0, es1) = splitAt n es
                      -- In case we matched constructor @c@ with @m@ arguments,
                      -- contract these @m@ arguments @vs@ to @Con c ci vs@.
                      patchCon c ci m es = patch (es0 ++ [VCon c ci vs <$ e] ++ es2)
                        where (es0, rest) = splitAt n es
                              (es1, es2)  = splitAt m rest
                              vs          = es1
                  -- Now do the matching on the @n@ths argument:
                  in case eb of
                    Blocked x _       -> no (Blocked x) es'
                    NotBlocked blk elim ->
                      case elim of
                        Apply (Arg info v) ->
                          case pushSubst v of
                            VClosure _ (MetaV x _) _ -> no (Blocked x) es'

                            -- In case of a natural number literal, try also its constructor form
                            VLit l@(LitNat r n) ->
                              let cFrame stack
                                    | n > 0                  = sucFrame (n - 1) stack
                                    | n == 0, Just z <- zero = conFrame z ConOSystem [] stack
                                    | otherwise              = stack
                              in match' steps f $ litFrame l $ cFrame $ catchAllFrame stack

                            VLit l    -> match' steps f $ litFrame l    $ catchAllFrame stack
                            VCon c ci vs -> match' steps f $ conFrame c ci vs $ catchAllFrame $ stack

                            -- Otherwise, we are stuck.  If we were stuck before,
                            -- we keep the old reason, otherwise we give reason StuckOn here.
                            _ -> no (NotBlocked $ stuckOn (fmap valueToTerm elim) blk) es'

                        -- In case of a projection, push the projFrame
                        Proj _ p -> match' steps f $ projFrame p stack


        -- If we reach the empty stack, then pattern matching was incomplete
        match' _ f [] = runReduce $ do
          pds <- getPartialDefs
          if f `elem` pds
          then return (NoReduction $ NotBlocked MissingClauses es)
          else do
            traceSLn "impossible" 10
              ("Incomplete pattern matching when applying " ++ show f)
              __IMPOSSIBLE__
