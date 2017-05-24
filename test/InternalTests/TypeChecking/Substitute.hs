
module InternalTests.TypeChecking.Substitute where

import Control.Arrow ((***), first, second)
import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Semigroup
import Data.Traversable (traverse)
import qualified Data.IntSet as Set
import Data.IntSet (IntSet)
import Test.QuickCheck

import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Free

import Agda.Utils.Pretty hiding ((<>))

import InternalTests.Helpers (runTests, quickCheckWith')

-- Contexts, types and terms ----------------------------------------------

infixr 1 :->
data Ty = A | B | C | X | Ty :-> Ty -- X denotes forbidden variables
  deriving (Eq, Ord, Show)

infixl 2 :>
data Cx = Nil | Cx :> Ty
  deriving (Eq, Ord, Show)

data Tm = VarT Int
        | AnnT Ty Tm
        | ConT Ty [Tm]
        | LamT Ty Tm
  deriving (Eq, Ord, Show)

varT :: Ty -> Int -> Tm
varT t x = AnnT t (VarT x)

type Sub = Substitution' Tm

-- Pretty printing --------------------------------------------------------

instance Pretty Cx where
  prettyPrec _ Nil = text "()"
  prettyPrec p g   = mparens (p > 2) $
    fsep $ punctuate comma $ map (prettyPrec 3) $ cxToList g

instance Pretty Ty where
  prettyPrec p t = case t of
    A -> text "A"
    B -> text "B"
    C -> text "C"
    X -> text "X"
    s :-> t -> mparens (p > 1) $
      hang (prettyPrec 2 s <+> text " -> ") 2 (prettyPrec 1 t)

instance Pretty Tm where
  prettyPrec = go [] vars
    where
      vars = [ c : i | i <- "" : map show [1..], c <- "xyz" ++ ['a'..'w'] ]
      go bound vars@(~(x : vars')) p v =
        case v of
          VarT i | i < length bound -> text (bound !! i)
                 | otherwise        -> text $ show (i - length bound)
          AnnT t v -> mparens (p > 0) $ hang (pp 1 v <+> text ":") 2 (pretty t)
          ConT t vs -> mparens (not (null vs) && p > 9) $
            text "Con" <+> fsep (prettyPrec 10 t : map (pp 10) vs)
          LamT t b -> mparens (p > 0) $
            hang (text $ "λ " ++ x ++ ".") 2 (go (x : bound) vars' 0 b)
        where
          pp = go bound vars

-- Helper functions -------------------------------------------------------

contextVars :: Cx -> [(Int, Ty)]
contextVars = go 0
  where
    go _ Nil      = []
    go i (g :> t) = (i, t) : go (i + 1) g

cxLen :: Cx -> Int
cxLen = length . contextVars

splitCx :: Int -> Cx -> (Cx, Cx)
splitCx 0 g        = (g, Nil)
splitCx n (g :> t) = second (:> t) $ splitCx (n - 1) g
splitCx _ Nil      = error "IMPOSSIBLE"

cxFromList :: [Ty] -> Cx
cxFromList = foldl (:>) Nil

cxToList :: Cx -> [Ty]
cxToList = reverse . map snd . contextVars

instance Semigroup Cx where
  gamma <> Nil = gamma
  gamma <> (delta :> t) = (gamma <> delta) :> t

instance Monoid Cx where
  mempty  = Nil
  mappend = (<>)

-- Substititution ---------------------------------------------------------

instance DeBruijn Tm where
  deBruijnView v = do VarT x <- pure v; pure x
  deBruijnVar x  = VarT x

instance Subst Tm Tm where
  applySubst rho v = case v of
    VarT x    -> lookupS rho x
    AnnT t v  -> AnnT t $ applySubst rho v
    ConT t vs -> ConT t $ map (applySubst rho) vs
    LamT t b  -> LamT t $ applySubst (liftS 1 rho) b

instance Free Tm where
  freeVars' v = case v of
    VarT x    -> variable x
    AnnT _ v  -> freeVars' v
    ConT _ vs -> freeVars' vs
    LamT _ b  -> freeVars' (Abs "" b)

-- Checking terms ---------------------------------------------------------

lookupCx :: Cx -> Int -> Maybe Ty
lookupCx Nil _       = empty
lookupCx _ n | n < 0 = empty
lookupCx (_ :> t) 0  = pure t
lookupCx (g :> _) n  = lookupCx g (n - 1)

getType :: Tm -> Ty
getType VarT{} = error "impossible: Vars should always be annotated!"
getType (AnnT t _) = t
getType (ConT t _) = t
getType (LamT t v) = t :-> getType v

inferTm :: Cx -> Tm -> Maybe Ty
inferTm g v =
  case v of
    VarT x -> lookupCx g x
    AnnT t v -> do
      s <- inferTm g v
      t <$ guard (t == s)
    ConT t vs -> t <$ mapM_ (inferTm g) vs
    LamT t v  -> (t :->) <$> inferTm (g :> t) v

checkTm :: Cx -> Tm -> Ty -> Bool
checkTm g v t = Just t == inferTm g v

-- Random generators ------------------------------------------------------

genBaseTy :: Gen Ty
genBaseTy = elements [A, B, C]

instance Arbitrary Ty where
  arbitrary = sized arb
    where
      arb n = frequency $
        [ (2, genBaseTy) ] ++
        [ (1, (:->) <$> genBaseTy <*> arb (div n 2)) | n > 0 ]

  shrink (s :-> t) =
    s : t : [ s :-> t | s <- shrink s ] ++
            [ s :-> t | t <- shrink t ]
  shrink _ = []

instance Arbitrary Cx where
  arbitrary = cxFromList <$> listOf (frequency [(3, genBaseTy), (1, pure X)])
  shrink (g :> t) =
    Nil : g : [ g :> t | g <- shrink g ] ++
              [ g :> t | t <- shrink t ]
  shrink _ = []

instance Arbitrary Tm where
  arbitrary = do
    g <- arbitrary
    t <- arbitrary
    genTm g t

  shrink (ConT t vs) = ConT t <$> shrink vs
  shrink v = [ConT (getType v) []]

genTm :: Cx -> Ty -> Gen Tm
genTm g t =
  frequency $
    [ (1, pure $ varT t x) | (x, s) <- contextVars g, s == t, s /= X ] ++
    [ (1, ConT t <$> do n <- choose (0, 3); vectorOf n (varOrLam g)) ] ++
    [ (4, LamT s <$> genTm (g :> s) t) | s :-> t <- [t] ]
  where
    varOrLam g =
      frequency $
        [ (1, pure $ varT t x) | (x, t) <- contextVars g, t /= X ] ++
        [ (1, do s <- genBaseTy; LamT s <$> varOrLam (g :> s)) ]

-- | Generate a random substitution for a given context.
--   If `(Γ, ρ) <- genSub Δ` then `Γ ⊢ ρ : Δ`.
genSub :: Cx -> Gen (Cx, Sub)
genSub delta = frequency $
  [ (1, pure (delta, IdS)) ] ++
  [ (1, (, EmptyS) <$> arbitrary) | delta == Nil ] ++
  [ (1, genCons g t) | g :> t <- [delta] ] ++
  [ (1, genWk delta) ] ++
  [ (1, genLift delta) | cxLen delta > 0 ]
  where
    genCons delta t = do
      (gamma, rho) <- genSub delta
      case t of
        X -> pure (gamma, Strengthen (error "str") rho)
        _ -> do
          v <- genTm gamma t
          pure (gamma, v :# rho)

    genWk delta = do
      n            <- choose (0, 3)
      psi          <- cxFromList <$> vectorOf n genBaseTy
      (gamma, rho) <- genSub delta
      pure (gamma <> psi, Wk n rho)

    genLift delta = do
      n <- choose (1, min 3 $ cxLen delta)
      let (delta1, delta2) = splitCx n delta
      (gamma, rho) <- genSub delta1
      pure (gamma <> delta2, Lift n rho)

genSub_ :: Cx -> Gen Sub
genSub_ g = snd <$> genSub g

-- Properties -------------------------------------------------------------

-- | Check that `Γ ⊢ ρ : Δ`, by testing on random terms `Δ ⊢ v`.
checkSub :: Cx -> Sub -> Cx -> Property
checkSub gamma rho delta =
  forAllShrink arbitrary shrink $ \ t ->
  forAllShrink (genTm delta t) shrink $ \ v ->
    whenFail (putStrLn $ "v[rho] = " ++ show (applySubst rho v)) $
    checkTm gamma (applySubst rho v) t

-- | Check that `ρ == σ : Δ` (don't need Γ) by generating random terms `Δ ⊢ v`
eqSub :: Sub -> Sub -> Cx -> Property
eqSub rho sgm delta =
  forAllShrink arbitrary shrink $ \ t ->
  forAllShrink (genTm delta t) shrink $ \ v ->
    applySubst rho v === applySubst sgm v

-- Generator properties --

prop_genTm :: Cx -> Ty -> Property
prop_genTm g t =
  forAll (genTm g t) $ \ v -> checkTm g v t

prop_genSub :: Cx -> Property
prop_genSub delta =
  forAll (genSub delta) $ \ (gamma, rho) ->
    checkSub gamma rho delta

-- Properties on substitution combinators --

-- | `wkS n rho == Wk n rho`
prop_wkS :: Cx -> Property
prop_wkS delta =
  forAllShrink (choose (0, 3)) shrink $ \ n ->
  forAll (genSub_ delta) $ \ rho ->
  eqSub (wkS n rho) (Wk n rho) delta

-- | `liftS n rho == Lift n rho`
prop_liftS :: Cx -> Cx -> Property
prop_liftS delta psi =
  forAll (genSub_ delta) $ \ rho ->
  eqSub (liftS n rho) (Lift n rho) (delta <> psi)
  where n = cxLen psi

-- | `consS v rho == v :# rho`
prop_consS :: Cx -> Ty -> Property
prop_consS delta t =
  forAll (genSub delta) $ \ (gamma, rho) ->
  forAll (genTm gamma t) $ \ v ->
  eqSub (consS v rho) (v :# rho) (delta :> t)

--   @
--               Γ, Δ ⊢ u : A
--    ---------------------------------
--    Γ, Δ ⊢ singletonS |Δ| u : Γ, A, Δ
--   @
prop_singletonS :: Cx -> Cx -> Ty -> Property
prop_singletonS gamma delta t =
  forAll (genTm (gamma <> delta) t) $ \ v ->
  checkSub (gamma <> delta) (singletonS (cxLen delta) v) ((gamma :> t) <> delta)

--   @
--             Γ, A, Δ ⊢ u : A
--    ---------------------------------
--    Γ, A, Δ ⊢ inplace |Δ| u : Γ, A, Δ
--   @
prop_inplaceS :: Cx -> Cx -> Ty -> Property
prop_inplaceS gamma delta t =
  forAll (genTm full t) $ \ v ->
  checkSub full (inplaceS (cxLen delta) v) full
  where
    full = (gamma :> t) <> delta

-- | @
--         Γ ⊢ ρ : Δ, Ψ
--      -------------------
--      Γ ⊢ dropS |Ψ| ρ : Δ
--   @
prop_dropS :: Cx -> Cx -> Property
prop_dropS delta psi =
  forAll (genSub (delta <> psi)) $ \ (gamma, rho) ->
  checkSub gamma (dropS (cxLen psi) rho) delta

-- | @
--        Γ ⊢ ρ : Δ, Ψ
--      -----------------  (σ, δ) = splitS |Ψ| ρ
--      Γ ⊢ σ : Δ
--      Γ ⊢ δ : Ψσ
--      σ == dropS |Ψ| ρ
--   @
prop_splitS :: Cx -> Cx -> Property
prop_splitS delta psi =
  forAll (genSub (delta <> psi)) $ \ (gamma, rho) ->
  let n = cxLen psi
      (sgm, dlt) = splitS n rho in
  checkSub gamma sgm delta .&&.
  checkSub gamma dlt psi   .&&.
  eqSub sgm (dropS n rho) delta

-- | @
--      Γ ⊢ ρ : Δ  Δ ⊢ σ : Θ
--      --------------------
--      Γ ⊢ composeS ρ σ : Θ
--   @
prop_composeS_type :: Cx -> Property
prop_composeS_type theta =
  forAll (genSub theta) $ \ (delta, sgm) ->
  forAll (genSub delta) $ \ (gamma, rho) ->
  checkSub gamma (composeS rho sgm) theta

-- | `applySubst (composeS ρ σ) == applySubst ρ . applySubst σ`
prop_composeS :: Cx -> Property
prop_composeS theta =
  forAll (genSub theta) $ \ (delta, sgm) ->
  forAll (genSub delta) $ \ (gamma, rho) ->
  forAll arbitrary $ \ t ->
  forAll (genTm theta t) $ \ v ->
  applySubst (composeS rho sgm) v === applySubst rho (applySubst sgm v)

-- | @
--     Γ ⊢ σ : Δ   Γ ⊢ ρ : Ψ, A, Θ
--    ------------------------------
--    Γ ⊢ lookupConsS ρ |Θ| σ : Δ, A
--   @
--   and
--   @
--      lookupConsS ρ i σ
--        | i ∈ support(ρ) = lookupS ρ i :# σ
--        | otherwise      = Strengthen σ
--   @
prop_lookupConsS :: Cx -> Cx -> Cx -> Ty -> Property
prop_lookupConsS delta psi theta t =
  forAll (genSub (delta <> (psi :> t) <> theta)) $ \ (gamma, sgmrho) ->
  let (sgm, rho) = splitS (cxLen psi + 1 + cxLen theta) sgmrho
      i          = cxLen theta
      sub        = lookupConsS rho i sgm in
  checkSub gamma sub (delta :> t) .&&.
  case t of
    X -> eqSub sub (Strengthen (error "lookupConsS") sgm) (delta :> t)
    _ -> eqSub sub (lookupS rho i :# sgm) (delta :> t)

-- | @
--      Γ ⊢ ρ : Δ  Γ ⊢ reverse vs : Θ
--      ----------------------------- (treating Nothing as having any type)
--        Γ ⊢ prependS vs ρ : Δ, Θ
--   @
prop_prependS :: Cx -> Property
prop_prependS delta =
  forAll (genSub delta) $ \ (gamma, rho) ->
  forAllShrink (listOf $ oneof [arbitrary, pure X]) shrink $ \ ts ->
  forAllShrink (mapM (mbyTerm gamma) $ reverse ts) (traverse . traverse $ shrink) $ \ vs ->
    checkSub gamma (prependS (error "prepend") vs rho) (delta <> cxFromList ts)
  where
    mbyTerm _     X = pure Nothing
    mbyTerm gamma t = Just <$> genTm gamma t

prop_parallelS :: Cx -> Cx -> Property
prop_parallelS gamma delta =
  forAllShrink (mapM (genTm gamma) (map snd $ contextVars delta)) (traverse shrink) $ \ vs ->
  checkSub gamma (parallelS vs) (gamma <> delta)

-- Properties about the free variable analysis --

-- | @
--             Γ ⊢ ρ : Δ      Δ ⊢ v : t
--      ----------------------------------------
--      freeLet ρ v == freeVars (applySubst ρ v)
--   @
prop_freeLet :: Cx -> Ty -> Property
prop_freeLet delta t =
  forAll       (genSub delta)         $ \ (gamma, rho) ->
  forAllShrink (genTm delta t) shrink $ \ v ->
  whenFail (debug gamma rho v) $
    run (freeLet rho v) === run (freeVars' $ applySubst rho v)
  where
    run :: FreeM IntSet IntSet -> [Int]
    run = Set.toList . runFreeM Set.singleton IgnoreNot

    debug gamma rho v = putStr $ unlines
      [ show $ sep [ pretty gamma <+> text "⊢"
                   , nest 2 $ text "ρ =" <+> pretty rho <+> text ":"
                   , nest 2 $ pretty delta ]
      , show $ text "v  =" <+> pretty v <+> text ":" <+> pretty t
      , show $ text "vρ =" <+> pretty (applySubst rho v)
      ]

qc :: Testable p => p -> IO Bool
qc = qc' 500

qc' :: Testable p => Int -> p -> IO Bool
qc' n p = quickCheckWith' stdArgs{maxSuccess = n} p

tests :: IO Bool
tests = tests' 500

tests' :: Int -> IO Bool
tests' n = runTests "InternalTests.TypeChecking.Substitute"
  [ qc' n prop_genTm
  , qc' n prop_genSub
  , qc' n prop_wkS
  , qc' n prop_liftS
  , qc' n prop_consS
  , qc' n prop_singletonS
  , qc' n prop_inplaceS
  , qc' n prop_dropS
  , qc' n prop_splitS
  , qc' n prop_composeS_type
  , qc' n prop_composeS
  , qc' n prop_lookupConsS
  , qc' n prop_prependS
  , qc' n prop_parallelS
  , qc' n prop_freeLet ]

