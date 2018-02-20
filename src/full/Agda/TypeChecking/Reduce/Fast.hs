{-# LANGUAGE CPP           #-}
{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}

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
import Control.Monad.ST
import Control.Monad.ST.Unsafe

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Traversable (traverse)
import Data.Foldable (toList)
import Data.Coerce

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef
import Data.STRef
import Data.Char
import qualified Data.Sequence as Seq

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
  | CCon  { cconSrcCon :: ConHead, cconArity :: Int }
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
      Constructor{conSrcCon = c, conArity = n} -> pure CCon{cconSrcCon = c, cconArity = n}
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

data IsValue = Value Blocked_
             | Unevaled

data Closure s = Closure IsValue Term (Env s) (Stack s)  -- Env applied to the Term (the stack contains closures)

isValue :: Closure s -> IsValue
isValue (Closure isV _ _ _) = isV

setIsValue :: IsValue -> Closure s -> Closure s
setIsValue isV (Closure _ t env stack) = Closure isV t env stack

type Env s = [Pointer s]

-- TODO: STRef
type Pointer s = STRef s (Thunk (Closure s))

data Thunk a = BlackHole | Thunk a
  deriving (Functor)

newPointer :: Closure s -> ST s (Pointer s)
newPointer cl = newSTRef (Thunk cl)

derefPointer :: Pointer s -> ST s (Thunk (Closure s))
derefPointer ptr = readSTRef ptr

derefPointer_ :: Pointer s -> ST s (Closure s)
derefPointer_ ptr = do
  Thunk cl <- derefPointer ptr
  return cl

storePointer :: Pointer s -> Closure s -> ST s ()
storePointer ptr cl = writeSTRef ptr (Thunk cl)

blackHole :: Pointer s -> ST s ()
blackHole ptr = writeSTRef ptr BlackHole

-- "Abstract" interface to environments

emptyEnv :: Env s
emptyEnv = []

isEmptyEnv :: Env s -> Bool
isEmptyEnv = null

envSize :: Env s -> Int
envSize = length

envToList :: Env s -> ST s [Closure s]
envToList = mapM derefPointer_

extendEnv :: Closure s -> Env s -> ST s (Env s)
extendEnv (Closure _ (Var x []) env' stack) env
  | isEmptyStack stack, Just p <- lookupEnv x env' = return (p : env)
extendEnv cl env = (: env) <$> newPointer cl

lookupEnv :: Int -> Env s -> Maybe (Pointer s)
lookupEnv i e | i < n     = Just (e !! i)
              | otherwise = Nothing
  where n = length e

-- End of Env API

type Stack s = StackC (Elim' (Closure s))

-- "Abstract" interface to stacks. Change StackC and the functions below to
-- change the representation of stacks.

type StackC     = []
type StackViewL = []

pattern (:<) :: a -> StackViewL a -> StackViewL a
pattern (:<) x xs = x : xs

pattern EmptyL :: StackViewL a
pattern EmptyL = []

infixr 5 :<|, :<, <|, ><

pattern (:<|) :: a -> StackC a -> StackC a
pattern (:<|) x xs = x : xs

(<|) :: a -> StackC a -> StackC a
(<|) = (:)

(><) :: StackC a -> StackC a -> StackC a
(><) = (++)

viewl :: StackC a -> StackViewL a
viewl = id

emptyStack :: StackC a
emptyStack = []

isEmptyStack :: StackC a -> Bool
isEmptyStack = null

stackFromList :: [a] -> StackC a
stackFromList = id

stackToList :: StackC a -> [a]
stackToList = id

splitStack :: Int -> StackC a -> (StackC a, StackC a)
splitStack = splitAt

indexStack :: StackC a -> Int -> a
indexStack = (!!)

-- End of stack API --

-- | Does not preserve 'IsValue'.
clApply :: Closure s -> Stack s -> Closure s
clApply c es' | isEmptyStack es' = c
clApply (Closure _ t env es) es' = Closure Unevaled t env (es >< es')

spliceStack :: StackC a -> a -> StackC a -> StackC a
spliceStack s0 e s1 = s0 >< e <| s1

type ControlStack s = [ControlFrame s]

data ControlFrame s = DoCase QName ArgInfo (Closure s) (FastCase FastCompiledClauses) Int (Stack s) (Stack s)
                    | DoForce QName (Stack s) (Stack s)
                    | NatSuc Integer
                    | PatchMatch (Stack s -> Stack s)
                    | FallThrough FastCompiledClauses
                    | DoPrimOp QName ([Literal] -> Term) [Literal] [Closure s] (Maybe FastCompiledClauses)
                    | UpdateThunk (Pointer s)
                    | DoApply (Stack s) -- To allow thunk updates before elimination

data Focus s = Eval (Closure s)
             | Match QName (Closure s) FastCompiledClauses (Stack s)
             | Mismatch QName (Closure s) (Stack s)
             | StuckMatch QName (Closure s) (Stack s)

type AM s = (Focus s, ControlStack s)

instance Pretty a => Pretty (Thunk a) where
  prettyPrec _ BlackHole  = text "<BLACKHOLE>"
  prettyPrec p (Thunk cl) = prettyPrec p cl

instance Pretty (Closure s) where
  prettyPrec p (Closure isV t env stack) =
    mparens (p > 9) $ fsep [ text tag
                           , nest 2 $ prettyPrec 10 t
                           , nest 2 $ text "_" -- prettyList $ zipWith envEntry [0..] env
                           , nest 2 $ prettyList (toList stack) ]
      where -- envEntry i c = text ("@" ++ show i ++ " =") <+> pretty (derefPointer c)
            tag = case isV of Value{} -> "V"; Unevaled -> "E"

instance Pretty (Focus s) where
  prettyPrec p (Eval cl)  = prettyPrec p cl
  prettyPrec p (Match _ cl cc st) = mparens (p > 9) $ (text "M" <?> prettyPrec 10 (clApply cl st)) <?> prettyPrec 10 cc
  prettyPrec p (Mismatch _ cl st) = mparens (p > 9) $ text "⊥" <?> prettyPrec 10 (clApply cl st)
  prettyPrec p (StuckMatch _ cl st) = mparens (p > 9) $ text "B" <?> prettyPrec 10 (clApply cl st)

instance Pretty (ControlFrame s) where
  prettyPrec p (DoCase f _ _ _ _ _ _)    = mparens (p > 9) $ text "DoCase" <+> text (show $ qnameName f)
  prettyPrec p (DoForce _ stack0 stack1) = mparens (p > 9) $ text "DoForce" <?> prettyList (toList $ stack0 >< stack1)
  prettyPrec _ (NatSuc n)                = text ("+" ++ show n)
  prettyPrec _ PatchMatch{}              = text "PatchMatch"
  prettyPrec p FallThrough{}             = text "FallThrough" -- mparens (p > 9) $ (text "FallThrough" <?> prettyList stack) <?> prettyPrec 10 cc
  prettyPrec p (DoPrimOp f _ vs cls _)   = mparens (p > 9) $ sep [ text "DoPrimOp" <+> pretty f
                                                                 , nest 2 $ prettyList vs
                                                                 , nest 2 $ prettyList cls ]
  prettyPrec p UpdateThunk{} = text "UpdateThunk"
  prettyPrec p (DoApply stack)           = mparens (p > 9) $ text "DoApply" <?> prettyList (toList stack)

compile :: Term -> AM s
compile t = (Eval (Closure Unevaled t emptyEnv emptyStack), [])

decodeClosure_ :: Closure s -> ST s Term
decodeClosure_ = ignoreBlocking <.> decodeClosure

decodeClosure :: Closure s -> ST s (Blocked Term)
decodeClosure (Closure isV t e st) = do
    -- Note: it's important to be lazy in the stack and environment here. Hence the
    -- unsafeInterleaveST's and special version of parallelS.
    vs <- unsafeInterleaveST $ mapM decodeClosure_ =<< envToList e
    es <- unsafeInterleaveST $ toList <$> (traverse . traverse) decodeClosure_ st
    return $ topMetaIsNotBlocked (applyE (applySubst (parS vs) t) es <$ b)
  where
    parS = foldr (:#) IdS  -- parallelS is too strict
    b = case isV of Value b  -> b
                    Unevaled -> notBlocked ()

elimsToStack :: Env s -> Elims -> Stack s
elimsToStack env es = seq (forceStack closures) stack
  where
    closures = (map . fmap) (mkClosure env) es
    stack    = stackFromList closures

    -- Need to be strict in mkClosure to avoid memory leak
    forceStack = foldl (\ () -> forceEl) ()
    forceEl (Apply (Arg _ Closure{})) = ()
    forceEl _ = ()

    mkClosure _ t@(Def f [])   = Closure Unevaled t emptyEnv emptyStack
    mkClosure _ t@(Con c i []) = Closure Unevaled t emptyEnv emptyStack
    mkClosure env t = Closure Unevaled t env emptyStack

reduceTm :: ReduceEnv -> (QName -> CompactDef) -> Bool -> Bool -> BuiltinEnv -> Term -> Blocked Term
reduceTm env !constInfo allowNonTerminating hasRewriting bEnv = compileAndRun . traceDoc (text "-- fast reduce --")
    -- fmap valueToTerm . reduceB' 0 . termToValue
  where
    BuiltinEnv{ bZero = zero, bSuc = suc } = bEnv

    metaStore = redSt env ^. stMetaStore

    sucCtrl :: ControlStack s -> ControlStack s
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

    rewriteRules f = cdefRewriteRules (constInfo f)

    hasVerb tag lvl = unReduceM (hasVerbosity tag lvl) env

    traceDoc
      | hasVerb "tc.reduce.fast" 110 = trace . show
      | otherwise                    = const id

    compileAndRun :: Term -> Blocked Term
    compileAndRun t = runST (runAM (compile t))

    runAM :: AM s -> ST s (Blocked Term)
    runAM s = traceDoc (pretty s) (runAM' s)

    runAM' :: AM s -> ST s (Blocked Term)
    runAM' (Eval cl@(Closure Value{} _ _ _), []) = decodeClosure cl
    runAM' s@(Eval cl@(Closure Unevaled t env stack), !ctrl) = -- The strict match is important!
      {-# SCC "runAM.Eval" #-}
      case t of

        Def f [] ->
          let CompactDef{ cdefDelayed        = delayed
                        , cdefNonterminating = nonterm
                        , cdefDef            = def } = constInfo f
              unfoldDelayed | DoCase{} : _ <- ctrl = True   -- only unfold delayed if there's a match on the stack
                            | otherwise            = False
              dontUnfold = (nonterm && not allowNonTerminating) ||
                           (delayed && not unfoldDelayed)
          in case def of
            CFun{ cfunCompiled = cc }
              | dontUnfold -> runAM done
              | otherwise  -> runAM (Match f (Closure Unevaled t emptyEnv emptyStack) cc stack, ctrl)
            CAxiom         -> rewriteAM done
            CTyCon         -> rewriteAM done
            CCon{}         -> runAM done   -- Only happens for builtinSharp (which is a Def when you bind it)
            COther         -> fallback s
            CForce | (stack0, Apply v :<| stack1) <- splitStack 4 stack ->
              runAM (Eval (unArg v), DoForce f stack0 stack1 : ctrl)
            CForce -> runAM done
            CPrimOp n op cc | length stack == n, Just (v : vs) <- allApplyElims (toList stack) ->
              runAM (Eval (unArg v), DoPrimOp f op [] (map unArg vs) cc : ctrl)
            CPrimOp{} -> runAM done  -- partially applied

        -- Nat zero
        Con c i [] | isZero c ->
          runAM (evalValueNoBlk (Lit (LitNat noRange 0)) emptyEnv stack, ctrl)

        -- Nat suc
        Con c i [] | isSuc c, Apply v :<| stack' <- stack ->
          runAM (Eval (unArg v), sucCtrl ctrl)

        Con c i [] ->
          case splitStack ar stack of
            (args, Proj _ p :<| stack') -> runAM (Eval (clApply (unArg arg) stack'), ctrl)
              where
                fields    = conFields c
                Just n    = List.elemIndex p fields
                Apply arg = indexStack args n
            _ -> rewriteAM (evalValueNoBlk (Con c' i []) env stack, ctrl)
          where CCon{cconSrcCon = c', cconArity = ar} = cdefDef (constInfo (conName c))

        Var x []   ->
          case lookupEnv x env of
            Nothing -> runAM (evalValue (notBlocked ()) (Var (x - envSize env) []) emptyEnv stack, ctrl)
            Just p  -> do
              thunk <- derefPointer p
              case thunk of
                BlackHole -> __IMPOSSIBLE__
                Thunk cl@(Closure Unevaled _ _ _) -> do
                  blackHole p
                  runAM (Eval cl, UpdateThunk p : [DoApply stack | not $ isEmptyStack stack] ++ ctrl)
                Thunk cl -> runAM (Eval (clApply cl stack), ctrl)

        MetaV m [] ->
          case mvInstantiation <$> Map.lookup m metaStore of
            Nothing -> __IMPOSSIBLE__
            Just inst  -> case inst of
              InstV xs t -> do
                ~(zs, env, stack') <- buildEnv xs stack
                runAM (evalClosure t env stack', ctrl)
              _          -> runAM (Eval (mkValue (blocked m ()) cl), ctrl)

        Lit{} -> runAM done
        Pi{}  -> runAM done

        Lam h b ->
          case viewl stack of
            Apply v :< stack' ->
              case b of
                Abs   _ b -> do
                  env' <- unArg v `extendEnv` env
                  runAM (evalClosure b env' stack', ctrl)
                NoAbs _ b -> runAM (evalClosure b env stack', ctrl)
            EmptyL -> runAM done
            _ -> __IMPOSSIBLE__

        Def f es   -> runAM (evalClosure (Def f [])   env $ elimsToStack env es >< stack, ctrl)
        Con c i es -> runAM (evalClosure (Con c i []) env $ elimsToStack env es >< stack, ctrl)
        Var x es   -> runAM (evalClosure (Var x [])   env $ elimsToStack env es >< stack, ctrl)
        MetaV m es -> runAM (evalClosure (MetaV m []) env $ elimsToStack env es >< stack, ctrl)

        _ -> fallback s
      where done = (Eval $ mkValue (notBlocked ()) cl, ctrl)

    -- +k continuations
    runAM' (Eval cl@(Closure Value{} (Lit (LitNat r n)) _ _), NatSuc m : ctrl) =
      runAM (evalValueNoBlk (Lit $! LitNat r $! m + n) emptyEnv emptyStack, ctrl)
    runAM' (Eval cl, NatSuc m : ctrl) = runAM (Eval stuck, ctrl)
      where
        stuck = mkValue (notBlocked ()) $ plus m cl
        plus 0 cl = cl
        plus n cl = valueNoBlk (Con (fromJust suc) ConOSystem [])
                               emptyEnv $ (Apply $ defaultArg $ plus (n - 1) cl) <| emptyStack

    -- builtin functions
    runAM' (Eval (Closure _ (Lit a) _ _), DoPrimOp f op vs es cc : ctrl) =
      case es of
        []      -> runAM (evalValueNoBlk (op (a : vs)) emptyEnv emptyStack, ctrl)
        e : es' -> runAM (Eval e, DoPrimOp f op (a : vs) es' cc : ctrl)
    runAM' (Eval cl@(Closure (Value blk) _ _ _), DoPrimOp f _ vs es mcc : ctrl) =
      case mcc of
        Nothing -> rewriteAM (Eval stuck, ctrl) -- Not a literal and no clauses: stuck
        Just cc -> runAM (Match f (Closure Unevaled (Def f []) emptyEnv emptyStack) cc stack, ctrl)
      where                                     -- otherwise try the clauses on non-literal
        stack     = fmap (Apply . defaultArg) $ spliceStack (stackFromList (map litClos (reverse vs))) cl (stackFromList es)
        litClos l = valueNoBlk (Lit l) emptyEnv emptyStack
        stuck     = Closure (Value blk) (Def f []) emptyEnv stack

    -- primForce
    runAM' (Eval arg@(Closure (Value blk) t _ _), DoForce pf stack0 stack1 : ctrl)
      | isWHNF t =
        case viewl stack1 of
          Apply k :< stack' -> runAM (Eval (clApply (unArg k) (Apply (defaultArg arg) <| stack')), ctrl)
          EmptyL            -> do
            -- primForce arg = λ k → k arg    (if whnf arg)
            let lam x = Lam defaultArgInfo . Abs x
            env <- extendEnv arg emptyEnv
            runAM (evalClosure (lam "k" $ Var 0 [Apply $ defaultArg $ Var 1 []])
                               env emptyStack, ctrl)
          _ -> __IMPOSSIBLE__
      | otherwise = rewriteAM (Eval stuck, ctrl)
      where
        stuck = Closure (Value blk) (Def pf []) emptyEnv $ spliceStack stack0 (Apply $ defaultArg arg) stack1
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

    -- Thunk update
    runAM' (Eval cl@(Closure Value{} _ _ _), UpdateThunk p : ctrl) =
      storePointer p cl >> runAM (Eval cl, ctrl)
    runAM' (Eval cl@(Closure Value{} _ _ _), DoApply stack : ctrl) =
      runAM (Eval (clApply cl stack), ctrl)

    -- Patching arguments on mismatch/stuck match
    runAM' (Mismatch f cl0 stack, PatchMatch patch : ctrl) =
      runAM (Mismatch f cl0 (patch stack), ctrl)
    runAM' (StuckMatch f cl0 stack, PatchMatch patch : ctrl) =
      runAM (StuckMatch f cl0 (patch stack), ctrl)

    -- Fall-through handling
    runAM' (Mismatch f cl0 stack, FallThrough cc : ctrl) =
      runAM (Match f cl0 cc stack, ctrl)
    runAM' (StuckMatch f cl0 stack, FallThrough{} : ctrl) =
      runAM (StuckMatch f cl0 stack, ctrl)
    runAM' (Mismatch f cl0 stack, ctrl) = rewriteAM s'
      where
        s' = runReduce $ do
          pds <- getPartialDefs
          if elem f pds then return (Eval (mkValue (NotBlocked MissingClauses ()) $ cl0 `clApply` stack), ctrl)
                        else do
            traceSLn "impossible" 10
              ("Incomplete pattern matching when applying " ++ show f)
              __IMPOSSIBLE__

    -- Recover from a stuck match
    runAM' (StuckMatch f cl0 stack, ctrl) = rewriteAM (Eval (mkValue blk $ clApply cl0 stack), ctrl)
      where Value blk = isValue cl0 -- cl0 should be a Value or we'd loop

    -- Impossible cases (we clean up FallThrough and PatchMatch frames before returning from a case)
    runAM' (Eval (Closure Value{} _ _ _), FallThrough{} : _) =
      __IMPOSSIBLE__
    runAM' (Eval (Closure Value{} _ _ _), PatchMatch{} : _) =
      __IMPOSSIBLE__

    -- Pattern matching against a value
    runAM' (Eval cl@(Closure (Value blk) t env stack), ctrl0@(DoCase f i cl0 bs n stack0 stack1 : ctrl)) =
      {-# SCC "runAM.DoCase" #-}
      case blk of
        Blocked{}    -> runAM =<< stuck
        NotBlocked{} -> case t of
          Con c ci [] | isSuc c -> sucFrame c ci $ catchallFrame $ runAM nomatch
          Con c ci [] -> conFrame c ci (length stack) $ catchallFrame $ runAM nomatch

          -- We can get here from a fallback (which builds a value without shifting args onto stack)
          Con c ci es -> runAM (evalValue blk (Con c ci []) emptyEnv (elimsToStack env es >< stack), ctrl0)

          -- Note: Literal natural number patterns are translated to suc-matches
          Lit (LitNat _ n) -> litsucFrame n $ zeroFrame n $ catchallFrame $ runAM nomatch

          Lit l -> litFrame l $ catchallFrame $ runAM nomatch

          _ -> runAM =<< stuck
          where
            -- Matching constructor
            conFrame c ci ar = lookupCon (conName c) bs =>? \ cc ->
              runAM (Match f cl0 cc (stack0 >< stack >< stack1),
                     PatchMatch (patchCon c ci ar) : ctrlFallThrough)

            -- Catch-all
            catchallFrame = fcatchAllBranch bs =>? \ cc ->
              runAM (Match f cl0 cc (spliceStack stack0 (Apply $ Arg i cl) stack1), ctrl)

            -- Matching literal
            litFrame l = Map.lookup l (flitBranches bs) =>? \ cc ->
              runAM (Match f cl0 cc (stack0 >< stack1),
                     PatchMatch patchWild : ctrlFallThrough)

            -- Matching a constructor against 'suc'
            sucFrame c ci | isSuc c =
              fsucBranch bs =>? \ cc ->
                runAM (Match f cl0 cc (stack0 >< stack >< stack1),
                       PatchMatch (patchSuc c ci) : ctrlFallThrough)
            sucFrame _ _ = id

            -- Matching a literal against 'suc'
            litsucFrame n | n <= 0 = id
            litsucFrame n = fsucBranch bs =>? \ cc ->
              runAM (Match f cl0 cc (spliceStack stack0 n' stack1),
                     PatchMatch (patchSuc (fromJust suc) ConOSystem) : ctrlFallThrough)
              where n' = Apply $ defaultArg $ valueNoBlk (Lit $! LitNat noRange $! n - 1) emptyEnv emptyStack

            -- Matching 'zero'
            zeroFrame n | n == 0, Just z <- zero = conFrame z ConOSystem 0
            zeroFrame _ = id

            patchSuc c ci es = spliceStack es0 (inc <$> arg) es1
              where (es0, rest) = splitStack n es
                    arg :< es1  = viewl rest
                    inc (Closure isV (Lit (LitNat r m)) _ _) = Closure isV (Lit $! LitNat r $! m + 1) emptyEnv emptyStack
                    inc t = valueNoBlk (Con c ci []) emptyEnv (Apply (defaultArg t) <| emptyStack)

            patchCon c ci ar es = spliceStack es0 (Apply $ Arg i $ valueNoBlk (Con c ci []) emptyEnv es1) es2
              where (es0, rest) = splitStack n es
                    (es1, es2)  = splitStack ar rest
      where
        patchWild es = spliceStack es0 (Apply $ Arg i cl) es1
          where (es0, es1) = splitStack n es

        stuck = do
            -- Compute new reason for being stuck. See
            -- Agda.Syntax.Internal.stuckOn for the logic.
            blk' <- case blk of
                      Blocked{}      -> return blk
                      NotBlocked r _ -> decodeClosure_ cl <&> \ v -> NotBlocked (stuckOn (Apply $ Arg i v) r) ()
            return (StuckMatch f (setIsValue (Value blk') cl0) stack', ctrl)
          where stack' = spliceStack stack0 (Apply $ Arg i cl) stack1

        -- Push catch-all frame if there is a catch-all
        ctrlFallThrough =
          case fcatchAllBranch bs of
            Nothing -> ctrl
            Just cc -> FallThrough cc : ctrl

        stack' = spliceStack stack0 (Apply $ Arg i cl) stack1

        nomatch = (Mismatch f cl0 stack', ctrl)

    runAM' (Match f cl0 cc stack, ctrl) =
      {-# SCC "runAM.Match" #-}
      case cc of
        -- impossible case
        FFail         -> runAM (StuckMatch f (mkValue (NotBlocked AbsurdMatch ()) cl0) stack, ctrl)
        FDone xs body -> do
            ~(zs, env, stack') <- buildEnv xs stack
            runAM (Eval (Closure Unevaled (lams zs body) env stack'), dropWhile matchy ctrl)
          where
            matchy PatchMatch{}  = True
            matchy FallThrough{} = True
            matchy DoCase{}      = False
            matchy DoForce{}     = False
            matchy NatSuc{}      = False
            matchy DoPrimOp{}    = False
            matchy UpdateThunk{} = False
            matchy DoApply{}     = False

            lams xs t = foldr lam t xs
            lam x t = Lam (argInfo x) (Abs (unArg x) t)

        -- Split on nth elimination on the stack
        FCase n bs ->
          case splitStack n stack of
            (stack0, st) -> case viewl st of
              -- If the nth elimination is not given, we're done
              EmptyL -> runAM (done Underapplied)
              -- apply elim: push the current match on the control stack and
              -- evaluate the argument
              Apply e :< stack1 -> runAM (Eval (unArg e), DoCase f (argInfo e) cl0 bs n stack0 stack1 : ctrl)
              -- projection elim
              e@(Proj o p) :< stack1 ->
                case lookupCon p bs of
                  Nothing -> runAM (done $ StuckOn (Proj o p)) -- No case for the projection: stop
                  Just cc -> runAM (Match f cl0 cc (stack0 >< stack1), PatchMatch patchProj : ctrl)
                where patchProj st = spliceStack st0 e st1
                        where (st0, st1) = splitStack n st
              _ -> __IMPOSSIBLE__  -- coverage checker can't do pattern synonyms!
      where done why = (StuckMatch f (mkValue (NotBlocked why ()) cl0) stack, ctrl)

    evalClosure t env stack = Eval (Closure Unevaled t env stack)

    evalValue b t env stack = Eval (Closure (Value b) t env stack)
    evalValueNoBlk = evalValue $ notBlocked ()
    valueNoBlk t env stack = Closure (Value $ notBlocked ()) t env stack

    mkValue b (Closure _ t env stack) = Closure (Value b) t env stack

    (=>?) :: Maybe a -> (a -> b) -> b -> b
    (m =>? f) z = maybe z f m

    fallback :: AM s -> ST s (Blocked Term)
    fallback (Eval c, ctrl) = do
        v <- decodeClosure_ c
        runAM (mkValue $ runReduce $ slowReduceTerm v, ctrl)
      where mkValue b = evalValue (() <$ b) (ignoreBlocking b) emptyEnv emptyStack
    fallback _ = __IMPOSSIBLE__

    rewriteAM :: AM s -> ST s (Blocked Term)
    rewriteAM s | not hasRewriting = runAM s
    rewriteAM s@(Eval (Closure (Value blk) t env stack), ctrl)
      | null rewr = runAM s
      | otherwise = traceDoc (text "R" <+> pretty s) $ do
        v0 <- decodeClosure_ (Closure Unevaled t env emptyStack)
        es <- toList <$> (traverse . traverse) decodeClosure_ stack
        case runReduce (rewrite blk v0 rewr es) of
          NoReduction b    -> runAM (evalValue (() <$ b) (ignoreBlocking b) emptyEnv emptyStack, ctrl)
          YesReduction _ v -> runAM (evalClosure v emptyEnv emptyStack, ctrl)
      where rewr = case t of
                     Def f []   -> rewriteRules f
                     Con c _ [] -> rewriteRules (conName c)
                     _          -> __IMPOSSIBLE__
    rewriteAM _ = __IMPOSSIBLE__

    -- Build the environment for a body with some given free variables from the
    -- top of the stack. Also returns the remaining stack and names for missing
    -- arguments in case of partial application.
    buildEnv :: [Arg String] -> Stack s -> ST s ([Arg String], Env s, Stack s)
    buildEnv xs stack = go xs stack emptyEnv
      where
        go [] st env = return ([], env, st)
        go xs0@(x : xs) st env =
          case viewl st of
            EmptyL        -> return (xs0, env, st)
            Apply c :< st -> go xs st =<< extendEnv (unArg c) env
            _             -> __IMPOSSIBLE__

