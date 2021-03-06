
module _ where

open import Common.Prelude

print : Float → IO Unit
print x = putStrLn (primShowFloat x)

printB : Bool → IO Unit
printB true  = putStrLn "true"
printB false = putStrLn "false"

_/_  = primFloatDiv
_==_ = primFloatEquality
_<_  = primFloatLess

NaN : Float
NaN = 0.0 / 0.0

-NaN : Float
-NaN = primFloatNegate NaN

Inf : Float
Inf = 1.0 / 0.0

-Inf : Float
-Inf = -1.0 / 0.0

sin   = primSin
cos   = primCos
tan   = primTan
asin  = primASin
acos  = primACos
atan  = primATan
atan2 = primATan2

main : IO Unit
main =
  putStr "123.4 = " ,, print 123.4 ,,
  putStr "-42.9 = " ,, print -42.9 ,,
  putStr "1.0   = " ,, print 1.0 ,,
  putStr "-0.0  = " ,, print -0.0  ,,
  putStr "NaN   = " ,, print NaN   ,,
  putStr "Inf   = " ,, print Inf   ,,
  putStr "-Inf  = " ,, print -Inf  ,,

  putStr "Inf == Inf = " ,, printB (Inf == Inf) ,,

  -- Issues #2155 and #2194.
  putStr "NaN == NaN = " ,, printB (NaN == NaN) ,,

  -- Issue #2169.
  putStr "0.0 == -0.0 = " ,, printB (0.0 == -0.0) ,,

  putStr "NaN  < -Inf = " ,, printB (NaN < -Inf) ,,
  putStr "0.0  < -0.0 = " ,, printB (0.0 < -0.0) ,,
  putStr "-0.0 < 0.0  = " ,, printB (-0.0 < 0.0) ,,

  -- Issue #2208.
  putStr "NaN  < NaN  = " ,, printB (NaN < NaN) ,,
  putStr "-NaN < -NaN = " ,, printB (-NaN < -NaN) ,,
  putStr "NaN  < -NaN = " ,, printB (NaN < -NaN) ,,

  putStr "sin (asin 0.6)      = " ,, print (sin (asin 0.6)) ,,
  putStr "cos (acos 0.6)      = " ,, print (cos (acos 0.6)) ,,
  putStr "tan (atan 0.4)      = " ,, print (tan (atan 0.4)) ,,
  putStr "tan (atan2 0.4 1.0) = " ,, print (tan (atan2 0.4 1.0)) ,,
  return unit
