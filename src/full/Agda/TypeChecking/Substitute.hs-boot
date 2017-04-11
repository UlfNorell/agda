module Agda.TypeChecking.Substitute where

import Agda.Syntax.Internal

applySubstTm :: Substitution -> Term -> Term
