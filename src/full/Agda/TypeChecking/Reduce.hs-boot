module Agda.TypeChecking.Reduce where

import Agda.Syntax.Internal (Term)
import Agda.TypeChecking.Monad.Base (TCM)

unfoldInlinedTCM :: Term -> TCM Term
