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
import Data.Char

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

import Agda.Utils.Float
import Agda.Utils.Lens
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
  | CAxiom  -- ^ Axiom or abstract defn
  | CPrimOp Int ([Literal] -> Term) (Maybe FastCompiledClauses)
      -- ^ Literals in reverse argument order
  | COther  -- ^ In this case we fall back to slow reduction

data BuiltinEnv = BuiltinEnv
  { bZero, bSuc, bTrue, bFalse :: Maybe ConHead
  , bPrimForce :: Maybe QName }

compactDef :: BuiltinEnv -> Definition -> RewriteRules -> ReduceM CompactDef
compactDef bEnv def rewr = do
  cdefn <-
    case theDef def of
      _ | Just (defName def) == bPrimForce bEnv -> pure CForce
      Constructor{conSrcCon = c} -> pure CCon{cconSrcCon = c}
      Function{funCompiled = Just cc, funClauses = _:_, funProjection = proj} ->
        pure CFun{ cfunCompiled   = fastCompiledClauses bEnv cc
                 , cfunProjection = projOrig <$> proj }
      Function{funClauses = []}      -> pure CAxiom
      Function{}                     -> pure COther -- Incomplete definition
      Datatype{dataClause = Nothing} -> pure CTyCon
      Record{recClause = Nothing}    -> pure CTyCon
      Datatype{}                     -> pure COther -- TODO
      Record{}                       -> pure COther -- TODO
      Axiom{}                        -> pure CAxiom
      AbstractDefn{}                 -> pure CAxiom
      Primitive{ primName = name, primCompiled = cc } ->
        case name of
          -- "primShowInteger" -- integers are not literals

          -- Natural numbers
          "primNatPlus"                -> mkPrim 2 $ natOp (+)
          "primNatMinus"               -> mkPrim 2 $ natOp (\ x y -> max 0 (x - y))
          "primNatTimes"               -> mkPrim 2 $ natOp (*)
          "primNatDivSucAux"           -> mkPrim 4 $ natOp4 divAux
          "primNatModSucAux"           -> mkPrim 4 $ natOp4 modAux
          "primNatLess"                -> mkPrim 2 $ natRel (<)
          "primNatEquality"            -> mkPrim 2 $ natRel (==)

          -- Word64
          "primWord64ToNat"            -> mkPrim 1 $ \ [LitWord64 _ a] -> nat (fromIntegral a)
          "primWord64FromNat"          -> mkPrim 1 $ \ [LitNat _ a]    -> word (fromIntegral a)

          -- Levels are not literals
          -- "primLevelZero"
          -- "primLevelSuc"
          -- "primLevelMax"

          -- Floats
          "primNatToFloat"             -> mkPrim 1 $ \ [LitNat _ a] -> float (fromIntegral a)
          "primFloatPlus"              -> mkPrim 2 $ floatOp (+)
          "primFloatMinus"             -> mkPrim 2 $ floatOp (-)
          "primFloatTimes"             -> mkPrim 2 $ floatOp (*)
          "primFloatNegate"            -> mkPrim 1 $ floatFun negate
          "primFloatDiv"               -> mkPrim 2 $ floatOp (/)
          "primFloatEquality"          -> mkPrim 2 $ floatRel floatEq
          "primFloatLess"              -> mkPrim 2 $ floatRel floatLt
          "primFloatNumericalEquality" -> mkPrim 2 $ floatRel (==)
          "primFloatNumericalLess"     -> mkPrim 2 $ floatRel (<)
          "primFloatSqrt"              -> mkPrim 1 $ floatFun sqrt
          -- "primRound"    -- Integers are not literals
          -- "primFloor"
          -- "primCeiling"
          "primExp"                    -> mkPrim 1 $ floatFun exp
          "primLog"                    -> mkPrim 1 $ floatFun log
          "primSin"                    -> mkPrim 1 $ floatFun sin
          "primCos"                    -> mkPrim 1 $ floatFun cos
          "primTan"                    -> mkPrim 1 $ floatFun tan
          "primASin"                   -> mkPrim 1 $ floatFun asin
          "primACos"                   -> mkPrim 1 $ floatFun acos
          "primATan"                   -> mkPrim 1 $ floatFun atan
          "primATan2"                  -> mkPrim 2 $ floatOp atan2
          "primShowFloat"              -> mkPrim 1 $ \ [LitFloat _ a] -> string (show a)

          -- Characters
          "primCharEquality"           -> mkPrim 2 $ charRel (==)
          "primIsLower"                -> mkPrim 1 $ charPred isLower
          "primIsDigit"                -> mkPrim 1 $ charPred isDigit
          "primIsAlpha"                -> mkPrim 1 $ charPred isAlpha
          "primIsSpace"                -> mkPrim 1 $ charPred isSpace
          "primIsAscii"                -> mkPrim 1 $ charPred isAscii
          "primIsLatin1"               -> mkPrim 1 $ charPred isLatin1
          "primIsPrint"                -> mkPrim 1 $ charPred isPrint
          "primIsHexDigit"             -> mkPrim 1 $ charPred isHexDigit
          "primToUpper"                -> mkPrim 1 $ charFun toUpper
          "primToLower"                -> mkPrim 1 $ charFun toLower
          "primCharToNat"              -> mkPrim 1 $ \ [LitChar _ a] -> nat (fromIntegral (fromEnum a))
          "primNatToChar"              -> mkPrim 1 $ \ [LitNat  _ a] -> char (toEnum $ fromIntegral $ a `mod` 0x110000)
          "primShowChar"               -> mkPrim 1 $ \ a -> string (show $ pretty a)

          -- Strings
          -- "primStringToList"     -- We don't have the list builtins (but could have, TODO)
          -- "primStringFromList"   -- and they are not literals
          "primStringAppend"           -> mkPrim 2 $ \ [LitString _ a, LitString _ b] -> string (b ++ a)
          "primStringEquality"         -> mkPrim 2 $ \ [LitString _ a, LitString _ b] -> bool (b == a)
          "primShowString"             -> mkPrim 1 $ \ a -> string (show $ pretty a)

          -- "primTrustMe"
          -- "primForce"
          -- "primForceLemma"
          "primQNameEquality"          -> mkPrim 2 $ \ [LitQName _ a, LitQName _ b] -> bool (b == a)
          "primQNameLess"              -> mkPrim 2 $ \ [LitQName _ a, LitQName _ b] -> bool (b < a)
          "primShowQName"              -> mkPrim 1 $ \ [LitQName _ a] -> string (show a)
          -- "primQNameFixity"  -- We don't have fixity builtins (TODO)
          "primMetaEquality"           -> mkPrim 2 $ \ [LitMeta _ _ a, LitMeta _ _ b] -> bool (b == a)
          "primMetaLess"               -> mkPrim 2 $ \ [LitMeta _ _ a, LitMeta _ _ b] -> bool (b < a)
          "primShowMeta"               -> mkPrim 1 $ \ [LitMeta _ _ a] -> string (show (pretty a))

          _                            -> pure COther
        where
          fcc = fastCompiledClauses bEnv <$> cc
          mkPrim n op = pure $ CPrimOp n op fcc

          divAux k m n j = k + div (max 0 $ n + m - j) (m + 1)
          modAux k m n j | n > j     = mod (n - j - 1) (m + 1)
                         | otherwise = k + n

          ~(Just true)  = bTrue  bEnv <&> \ c -> Con c ConOSystem []
          ~(Just false) = bFalse bEnv <&> \ c -> Con c ConOSystem []

          bool   a = if a then true else false
          nat    a = Lit . LitNat    noRange $! a
          word   a = Lit . LitWord64 noRange $! a
          float  a = Lit . LitFloat  noRange $! a
          string a = Lit . LitString noRange $! a
          char   a = Lit . LitChar   noRange $! a

          -- Remember reverse order!
          natOp f [LitNat _ a, LitNat _ b] = nat (f b a)
          natOp _ _ = __IMPOSSIBLE__

          natOp4 f [LitNat _ a, LitNat _ b, LitNat _ c, LitNat _ d] = nat (f d c b a)
          natOp4 _ _ = __IMPOSSIBLE__

          natRel f [LitNat _ a, LitNat _ b] = bool (f b a)
          natRel _ _ = __IMPOSSIBLE__

          floatFun f [LitFloat _ a] = float (f a)
          floatFun _ _ = __IMPOSSIBLE__

          floatOp f [LitFloat _ a, LitFloat _ b] = float (f b a)
          floatOp _ _ = __IMPOSSIBLE__

          floatRel f [LitFloat _ a, LitFloat _ b] = bool (f b a)
          floatRel _ _ = __IMPOSSIBLE__

          charFun f [LitChar _ a] = char (f a)
          charFun _ _ = __IMPOSSIBLE__

          charPred f [LitChar _ a] = bool (f a)
          charPred _ _ = __IMPOSSIBLE__

          charRel f [LitChar _ a, LitChar _ b] = bool (f b a)
          charRel _ _ = __IMPOSSIBLE__

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

fastCompiledClauses :: BuiltinEnv -> CompiledClauses -> FastCompiledClauses
fastCompiledClauses bEnv cc =
  case cc of
    Fail              -> FFail
    Done xs b         -> FDone xs b
    Case (Arg _ n) bs -> FCase n (fastCase bEnv bs)

fastCase :: BuiltinEnv -> Case CompiledClauses -> FastCase FastCompiledClauses
fastCase env (Branches proj con lit wild _) =
  FBranches
    { fprojPatterns   = proj
    , fconBranches    = Map.mapKeysMonotonic (nameId . qnameName) $ fmap (fastCompiledClauses env . content) (stripSuc con)
    , fsucBranch      = fmap (fastCompiledClauses env . content) $ flip Map.lookup con . conName =<< bSuc env
    , flitBranches    = fmap (fastCompiledClauses env) lit
    , fcatchAllBranch = fmap (fastCompiledClauses env) wild }
  where
    stripSuc | Just c <- bSuc env = Map.delete (conName c)
             | otherwise          = id

instance Pretty a => Pretty (FastCase a) where
  prettyPrec p (FBranches _cop cs suc ls m) =
    mparens (p > 0) $ vcat (prettyMap cs ++ prettyMap ls ++ prSuc suc ++ prC m)
    where
      prC Nothing = []
      prC (Just x) = [text "_ ->" <?> pretty x]

      prSuc Nothing  = []
      prSuc (Just x) = [text "suc ->" <?> pretty x]

instance Pretty NameId where
  pretty = text . show

instance Pretty FastCompiledClauses where
  pretty (FDone xs t) = (text "done" <+> prettyList xs) <?> prettyPrec 10 t
  pretty FFail        = text "fail"
  pretty (FCase n bs) | fprojPatterns bs =
    sep [ text "record"
        , nest 2 $ pretty bs
        ]
  pretty (FCase n bs) =
    text ("case " ++ prettyShow n ++ " of") <?> pretty bs

-- type FastStack = [(FastCompiledClauses, [MaybeReduced (Elim' Value)], [Elim' Value] -> [Elim' Value])]

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
-- strictSubst :: Bool -> [Term] -> Term -> Term
-- strictSubst strict us
--   | not strict = applySubst rho
--   | otherwise  = go 0
--   where
--     rho = parallelS us
--     go k v =
--       case v of
--         Var x es
--           | x < k     -> Var x $! map' (goE k) es
--           | otherwise -> applyE (raise k $ us !! (x - k)) $! map' (goE k) es
--         Def f es -> defApp f [] $! map' (goE k) es
--         Con c ci es -> Con c ci $! map' (goE k) es
--         Lam i b  -> Lam i $! goAbs k b
--         Lit{}    -> v
--         _        -> applySubst (liftS k rho) v

--     goE k (Apply v) = Apply $! mapArg' (go k) v
--     goE _ p         = p

--     goAbs k (Abs   x v) = Abs   x $! go (k + 1) v
--     goAbs k (NoAbs x v) = NoAbs x $! go k v

-- map' :: (a -> b) -> [a] -> [b]
-- map' f []       = []
-- map' f (x : xs) = ((:) $! f x) $! map' f xs

-- mapArg' :: (a -> b) -> Arg a -> Arg b
-- mapArg' f (Arg i x) = Arg i $! f x


-- Fast reduction ---------------------------------------------------------

-- | First argument: allow non-terminating reductions.
fastReduce :: Bool -> Term -> ReduceM (Blocked Term)
fastReduce allowNonTerminating v = do
  let name (Con c _ _) = c
      name _         = __IMPOSSIBLE__
  zero  <- fmap name <$> getBuiltin' builtinZero
  suc   <- fmap name <$> getBuiltin' builtinSuc
  force <- fmap primFunName <$> getPrimitive' "primForce"
  true  <- fmap name <$> getBuiltin' builtinTrue
  false <- fmap name <$> getBuiltin' builtinFalse
  let bEnv = BuiltinEnv { bZero = zero, bSuc = suc, bTrue = true, bFalse = false, bPrimForce = force }
  rwr <- optRewriting <$> pragmaOptions
  constInfo <- unKleisli $ \f -> do
    info <- getConstInfo f
    rewr <- if rwr then instantiateRewriteRules =<< getRewriteRulesFor f
                   else return []
    compactDef bEnv info rewr
  ReduceM $ \ env -> reduceTm env (memoQName constInfo) allowNonTerminating rwr bEnv v

unKleisli :: (a -> ReduceM b) -> ReduceM (a -> b)
unKleisli f = ReduceM $ \ env x -> unReduceM (f x) env

-- | For some reason...
topMetaIsNotBlocked :: Blocked Term -> Blocked Term
topMetaIsNotBlocked (Blocked _ t@MetaV{}) = notBlocked t
topMetaIsNotBlocked b = b

data IsValue = Value (Blocked ())
             | Unevaled

data Closure = Closure IsValue Term Env Stack  -- Env applied to the Term (the stack contains closures)
type Env = [Closure]

isValue :: Closure -> IsValue
isValue (Closure isV _ _ _) = isV

setIsValue :: IsValue -> Closure -> Closure
setIsValue isV (Closure _ t env stack) = Closure isV t env stack

lookupEnv :: Int -> Env -> Maybe Closure
lookupEnv i e | i < length e = Just (e !! i)
              | otherwise    = Nothing

type Stack = [Elim' Closure]

-- | Does not preserve 'IsValue'.
clApply :: Closure -> Stack -> Closure
clApply c                    []  = c
clApply (Closure _ t env es) es' = Closure Unevaled t env (es ++ es')

type ControlStack = [ControlFrame]

data ControlFrame = DoCase QName ArgInfo Closure (FastCase FastCompiledClauses) Int Stack Stack
                  | DoForce QName Stack Stack
                  | NatSuc Integer
                  | PatchMatch (Stack -> Stack)
                  | FallThrough FastCompiledClauses
                  | DoPrimOp QName ([Literal] -> Term) [Literal] [Closure] (Maybe FastCompiledClauses)

data Focus = Eval Closure
           | Match QName Closure FastCompiledClauses Stack
           | Mismatch QName Closure Stack
           | StuckMatch QName Closure Stack

type AM = (Focus, ControlStack)

instance Pretty Closure where
  prettyPrec p (Closure isV t env stack) =
    mparens (p > 9) $ fsep [ text tag
                           , nest 2 $ prettyPrec 10 t
                           , nest 2 $ text "_" -- prettyList $ zipWith envEntry [0..] env
                           , nest 2 $ prettyList stack ]
      where envEntry i c = text ("@" ++ show i ++ " =") <+> pretty c
            tag = case isV of Value{} -> "V"; Unevaled -> "E"

instance Pretty Focus where
  prettyPrec p (Eval cl)  = prettyPrec p cl
  prettyPrec p (Match _ cl cc st) = mparens (p > 9) $ (text "M" <?> prettyPrec 10 (clApply cl st)) <?> prettyPrec 10 cc
  prettyPrec p (Mismatch _ cl st) = mparens (p > 9) $ text "⊥" <?> prettyPrec 10 (clApply cl st)
  prettyPrec p (StuckMatch _ cl st) = mparens (p > 9) $ text "B" <?> prettyPrec 10 (clApply cl st)

instance Pretty ControlFrame where
  prettyPrec _ DoCase{}      = text "DoCase{}"
  prettyPrec p (DoForce _ stack0 stack1)  = mparens (p > 9) $ text "DoForce" <?> prettyList (stack0 ++ stack1)
  prettyPrec _ (NatSuc n)    = text ("+" ++ show n)
  prettyPrec _ PatchMatch{}  = text "PatchMatch{}"
  prettyPrec p FallThrough{} = text "FallThrough{}" -- mparens (p > 9) $ (text "FallThrough" <?> prettyList stack) <?> prettyPrec 10 cc
  prettyPrec p (DoPrimOp f _ vs cls _) = mparens (p > 9) $ sep [ text "DoPrimOp" <+> pretty f
                                                                , nest 2 $ prettyList vs
                                                                , nest 2 $ prettyList cls ]

compile :: Term -> AM
compile t = (Eval (Closure Unevaled t [] []), [])

decodeClosure :: Closure -> Blocked Term
decodeClosure (Closure isV t [] st) = applyE t ((map . fmap) (ignoreBlocking . decodeClosure) st) <$ b
  where b = case isV of Value b -> b; Unevaled -> notBlocked ()
decodeClosure (Closure isV t e st)  = decodeClosure (Closure isV (applySubst rho t) [] st)
  where rho  = parS (map (ignoreBlocking . decodeClosure) e)
        parS = foldr (:#) IdS  -- parallelS is too strict

elimsToStack :: Env -> Elims -> Stack
elimsToStack env es = seq (forceStack stack) stack
  where
    stack = (map . fmap) (mkClosure env) es

    -- Need to be strict in mkClosure to avoid memory leak
    forceStack = foldl (\ () -> forceEl) ()
    forceEl (Apply (Arg _ Closure{})) = ()
    forceEl _ = ()

    -- The Var case is crucial, the Def and Con makes little difference
    mkClosure env (Var x es) | Just c <- lookupEnv x env = clApply c (elimsToStack env es)
    mkClosure env t@(Def f [])   = Closure Unevaled t [] []
    mkClosure env t@(Con c i []) = Closure Unevaled t [] []
    mkClosure env t = Closure Unevaled t env []

reduceTm :: ReduceEnv -> (QName -> CompactDef) -> Bool -> Bool -> BuiltinEnv -> Term -> Blocked Term
reduceTm env !constInfo allowNonTerminating hasRewriting bEnv = runAM . compile . traceDoc (text "-- fast reduce --")
    -- fmap valueToTerm . reduceB' 0 . termToValue
  where
    BuiltinEnv{ bZero = zero, bSuc = suc } = bEnv

    metaStore = redSt env ^. stMetaStore

    sucCtrl :: ControlStack -> ControlStack
    sucCtrl (NatSuc n : ctrl) = (NatSuc $! n + 1) : ctrl
    sucCtrl ctrl              = NatSuc 1 : ctrl

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

    isTyCon q =
      case cdefDef $ constInfo q of
        CTyCon -> True
        _      -> False

    hasVerb tag lvl = unReduceM (hasVerbosity tag lvl) env

    traceDoc
      | hasVerb "tc.reduce.fast" 110 = trace . show
      | otherwise                    = const id

    -- runAM s = runAM' s
    runAM s = traceDoc (pretty s) (runAM' s)

    runAM' :: AM -> Blocked Term
    runAM' (Eval cl@(Closure Value{} _ _ _), []) = decodeClosure cl
    runAM' s@(Eval cl@(Closure Unevaled t env stack), !ctrl) = -- The strict match is important!
      case t of

        Def f [] ->
          case cdefDef (constInfo f) of
            CFun{ cfunCompiled = cc } -> runAM (Match f (Closure Unevaled t [] []) cc stack, ctrl)
            CAxiom                    -> runAM done
            CTyCon                    -> runAM done
            CCon{}                    -> __IMPOSSIBLE__
            COther                    -> fallback s
            CForce | (stack0, Apply v : stack1) <- splitAt 4 stack ->
              runAM (Eval (unArg v), DoForce f stack0 stack1 : ctrl)
            CForce -> runAM done
            CPrimOp n op cc | length stack == n, Just (v : vs) <- allApplyElims stack ->
              runAM (Eval (unArg v), DoPrimOp f op [] (map unArg vs) cc : ctrl)
            CPrimOp{} -> runAM done  -- partially applied

        -- Nat zero
        Con c i [] | isZero c ->
          runAM (evalValueNoBlk (Lit (LitNat noRange 0)) [] stack, ctrl)

        -- Nat suc
        Con c i [] | isSuc c, Apply v : stack' <- stack ->
          runAM (Eval (unArg v), sucCtrl ctrl)

        Con c i [] -> runAM (evalValueNoBlk (Con c' i []) env stack, ctrl)
          where CCon{cconSrcCon = c'} = cdefDef (constInfo (conName c))
          -- TODO: projection

        Var x []   ->
          case lookupEnv x env of
            Nothing -> runAM done
            Just cl -> runAM (Eval (clApply cl stack), ctrl)

        MetaV m [] ->
          case mvInstantiation <$> Map.lookup m metaStore of
            Nothing -> __IMPOSSIBLE__
            Just inst  -> case inst of
              InstV xs t -> runAM (evalClosure t env stack', ctrl)
                where (zs, env, stack') = buildEnv xs stack
              _          -> runAM (Eval (mkValue (blocked m ()) cl), ctrl)

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
      where done = (Eval $ mkValue (notBlocked ()) cl, ctrl)

    -- +k continuations
    runAM' s@(Eval cl@(Closure Value{} t _ stack), NatSuc m : ctrl) =
      case (t, stack) of
        (Lit (LitNat r n), []) ->
          runAM (evalValueNoBlk (Lit $! LitNat r $! m + n) [] [], ctrl)
        _ -> runAM (Eval stuck, ctrl)
      where
        stuck = mkValue (notBlocked ()) $ plus m cl
        -- TODO: optimised representation of sucⁿ t
        plus 0 cl = cl
        plus n cl = Closure (Value $ notBlocked ())
                            (Con (fromJust suc) ConOSystem [])
                            [] [Apply $ defaultArg $ plus (n - 1) cl]

    -- builtin functions
    runAM' (Eval (Closure _ (Lit a) _ []), DoPrimOp f op vs es cc : ctrl) =
      case es of
        []      -> runAM (evalValueNoBlk (op (a : vs)) [] [], ctrl)
        e : es' -> runAM (Eval e, DoPrimOp f op (a : vs) es' cc : ctrl)
    runAM' (Eval cl@(Closure (Value blk) _ _ _), DoPrimOp f _ vs es mcc : ctrl) =
      case mcc of
        Nothing -> runAM (Eval stuck, ctrl)                                           -- Not a literal and no clauses: stuck
        Just cc -> runAM (Match f (Closure Unevaled (Def f []) [] []) cc stack, ctrl) -- otherwise try the clauses on non-literal
      where
        stack     = map (Apply . defaultArg) $ map litClos (reverse vs) ++ [cl] ++ es
        litClos l = Closure (Value $ notBlocked ()) (Lit l) [] []
        stuck     = Closure (Value blk) (Def f []) [] stack

    -- primForce
    runAM' (Eval arg@(Closure (Value blk) t _ _), DoForce pf stack0 stack1 : ctrl)
      | isWHNF t =
        case stack1 of
          Apply k : stack' -> runAM (Eval (clApply (unArg k) (Apply (defaultArg arg) : stack')), ctrl)
          _ : _            -> __IMPOSSIBLE__
          []               -> __IMPOSSIBLE__    -- TODO: need to build \ k -> k arg
      | otherwise = runAM (Eval stuck, ctrl)
      where
        stuck = Closure (Value blk) (Def pf []) [] $ stack0 ++ [Apply $ defaultArg arg] ++ stack1
        isWHNF u = case u of
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

    -- Patching arguments on mismatch/stuck match
    runAM' s@(Mismatch f cl0 stack, PatchMatch patch : ctrl) =
      runAM (Mismatch f cl0 (patch stack), ctrl)
    runAM' s@(StuckMatch f cl0 stack, PatchMatch patch : ctrl) =
      runAM (StuckMatch f cl0 (patch stack), ctrl)

    -- Fall-through handling
    runAM' s@(Mismatch f cl0 stack, FallThrough cc : ctrl) =
      runAM (Match f cl0 cc stack, ctrl)
    runAM' s@(StuckMatch f cl0 stack, FallThrough{} : ctrl) =
      runAM (StuckMatch f cl0 stack, ctrl)
    runAM' s@(Mismatch f cl0 stack, ctrl) =   -- TODO: fail unless f `elem` partialDefs
      runAM (Eval (mkValue (NotBlocked MissingClauses ()) $ cl0 `clApply` stack), ctrl)


    -- Recover from a stuck match
    runAM' (StuckMatch f cl0 stack, ctrl) = runAM (Eval (mkValue blk $ clApply cl0 stack), ctrl)
      where Value blk = isValue cl0 -- cl0 should be a Value or we'd loop

    -- Impossible cases (we clean up FallThrough and PatchMatch frames before returning from a case)
    runAM' (Eval (Closure Value{} _ _ _), FallThrough{} : _) =
      __IMPOSSIBLE__
    runAM' (Eval (Closure Value{} _ _ _), PatchMatch{} : _) =
      __IMPOSSIBLE__

    -- Pattern matching against a value
    runAM' s@(Eval cl@(Closure (Value blk) t env stack), DoCase f i cl0 bs n stack0 stack1 : ctrl) =
      case blk of
        Blocked{}    -> runAM stuck
        NotBlocked{} -> case t of
          Con c ci [] | isSuc c -> sucFrame c ci $ catchallFrame $ runAM nomatch
          Con c ci [] -> conFrame c ci (length stack) $ catchallFrame $ runAM nomatch

          Con{} -> __IMPOSSIBLE__ -- elims should have been shifted onto the stack

          -- Note: Literal natural number patterns are translated to suc-matches
          Lit (LitNat _ n) -> litsucFrame n $ zeroFrame n $ catchallFrame $ runAM nomatch

          Lit l -> litFrame l $ catchallFrame $ runAM nomatch

          _ -> runAM stuck
          where
            -- Matching constructor
            conFrame c ci ar = lookupCon (conName c) bs =>? \ cc ->
              runAM (Match f cl0 cc (stack0 ++ stack ++ stack1),
                     PatchMatch (patchCon c ci ar) : ctrlFallThrough)

            -- Catch-all
            catchallFrame = fcatchAllBranch bs =>? \ cc ->
              runAM (Match f cl0 cc (stack0 ++ [Apply $ Arg i cl] ++ stack1), ctrl)

            -- Matching literal: TODO might fall through to constructor cases!
            litFrame l = Map.lookup l (flitBranches bs) =>? \ cc ->
              runAM (Match f cl0 cc (stack0 ++ stack1),
                     PatchMatch patchWild : ctrlFallThrough)

            -- Matching a constructor against 'suc'
            sucFrame c ci | isSuc c =
              fsucBranch bs =>? \ cc ->
                runAM (Match f cl0 cc (stack0 ++ stack ++ stack1),
                       PatchMatch (patchCon c ci 1) : ctrlFallThrough)
            sucFrame _ _ = id

            -- Matching a literal against 'suc'
            litsucFrame n | n <= 0 = id
            litsucFrame n = fsucBranch bs =>? \ cc ->
              runAM (Match f cl0 cc (stack0 ++ [n'] ++ stack1),
                     PatchMatch (patchCon (fromJust suc) ConOSystem 1) : ctrlFallThrough)
              where n' = Apply $ defaultArg $ Closure (Value $ notBlocked ()) (Lit $! LitNat noRange $! n - 1) [] []

            -- Matching 'zero'
            zeroFrame n | n == 0, Just z <- zero = conFrame z ConOSystem 0
            zeroFrame _ = id

            patchCon c ci ar es = es0 ++ [Apply $ Arg i $ Closure (Value $ notBlocked ()) (Con c ci []) [] es1] ++ es2
              where (es0, rest) = splitAt n es
                    (es1, es2)  = splitAt ar rest
      where
        patchWild es = es0 ++ [Apply $ Arg i cl] ++ es1
          where (es0, es1) = splitAt n es

        -- TODO: keeps the reason from the arg (old code used StuckOn elim for some cases..)
        stuck = (StuckMatch f (setIsValue (Value blk) cl0) stack', ctrl)
          where stack' = stack0 ++ [Apply $ Arg i cl] ++ stack1

        -- Push catch-all frame if there is a catch-all
        ctrlFallThrough =
          case fcatchAllBranch bs of
            Nothing -> ctrl
            Just cc -> FallThrough cc : ctrl

        stack' = stack0 ++ [Apply $ Arg i cl] ++ stack1

        nomatch = (Mismatch f cl0 stack', ctrl)

    runAM' s@(Match f cl0 cc stack, ctrl) =
      case cc of
        -- impossible case
        FFail         -> runAM (StuckMatch f (mkValue (NotBlocked AbsurdMatch ()) cl0) stack, ctrl)
        FDone xs body -> runAM (Eval (Closure Unevaled (lams zs body) env stack'), dropWhile matchy ctrl)
          where
            matchy PatchMatch{}  = True
            matchy FallThrough{} = True
            matchy DoCase{}      = False
            matchy DoForce{}     = False
            matchy NatSuc{}      = False
            matchy DoPrimOp{}    = False
            (zs, env, stack') = buildEnv xs stack

            lams xs t = foldr lam t xs
            lam x t = Lam (argInfo x) (Abs (unArg x) t)

        -- Split on nth elimination on the stack
        FCase n bs ->
          case splitAt n stack of
            -- If the nth elimination is not given, we're done
            (_, []) -> runAM (done Underapplied)
            -- apply elim: push the current match on the control stack and
            -- evaluate the argument
            (stack0, Apply e : stack1) -> runAM (Eval (unArg e), DoCase f (argInfo e) cl0 bs n stack0 stack1 : ctrl)
            -- projection elim
            (stack0, e@(Proj o p) : stack1) ->
              case lookupCon p bs of
                Nothing -> runAM (done $ StuckOn (Proj o p)) -- No case for the projection: stop
                Just cc -> runAM (Match f cl0 cc (stack0 ++ stack1), PatchMatch patchProj : ctrl)
              where patchProj st = st0 ++ [e] ++ st1
                      where (st0, st1) = splitAt n st
      where done why = (StuckMatch f (mkValue (NotBlocked why ()) cl0) stack, ctrl)

    evalClosure t env stack = Eval (Closure Unevaled t env stack)

    evalValue b t env stack = Eval (Closure (Value b) t env stack)
    evalValueNoBlk = evalValue $ notBlocked ()

    mkValue b (Closure _ t env stack) = Closure (Value b) t env stack

    (=>?) :: Maybe a -> (a -> b) -> b -> b
    (m =>? f) z = maybe z f m

    fallback :: AM -> Blocked Term
    fallback (Eval c, ctrl) = runAM (mkValue $ runReduce $ slowReduceTerm $ ignoreBlocking $ decodeClosure c, ctrl)
      where mkValue b = evalValue (() <$ b) (ignoreBlocking b) [] []
    fallback _ = __IMPOSSIBLE__

    -- Build the environment for a body with some given free variables from the
    -- top of the stack. Also returns the remaining stack and names for missing
    -- arguments in case of partial application.
    buildEnv :: [Arg String] -> Stack -> ([Arg String], Env, Stack)
    buildEnv xs stack = go xs stack []
      where
        go xs       []             env = (xs, env, [])
        go []       st             env = ([], env, st)
        go (x : xs) (Apply c : st) env = go xs st (unArg c : env)
        go (_ : _)  (_ : _)        _   = __IMPOSSIBLE__

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
