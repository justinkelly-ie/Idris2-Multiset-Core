module Math.Spread

import Data.Vect
import Math.BoxInt

%default total

------------------------------------------------------------------------
-- SPREAD POLYNOMIAL RECURRENCE OVER LISTS
------------------------------------------------------------------------

||| Adds two polynomial lists coefficient-wise.
public export
addList : List BoxInt -> List BoxInt -> List BoxInt
addList [] ys = ys
addList xs [] = xs
addList (x :: xs) (y :: ys) = (x + y) :: addList xs ys

||| Scales a polynomial list by a BoxInt scalar.
public export
scaleList : BoxInt -> List BoxInt -> List BoxInt
scaleList s xs = map (s *) xs

||| Recursive list generation of Wildberger's Spread Polynomials Sn(s):
||| S_0(s) = 0
||| S_1(s) = s
||| S_n(s) = 2*(1 - 2*s)*S_{n-1}(s) - S_{n-2}(s) + 2*s
public export
spreadList : Nat -> List BoxInt
spreadList Z = [intToBoxInt 0]
spreadList (S Z) = [intToBoxInt 0, intToBoxInt 1]
spreadList (S (S k)) =
  let s1 = spreadList (S k)
      s2 = spreadList k
      term1 = scaleList (intToBoxInt 2) s1
      term2 = intToBoxInt 0 :: scaleList (intToBoxInt (-4)) s1
      term3 = scaleList (intToBoxInt (-1)) s2
      term4 = [intToBoxInt 0, intToBoxInt 2]
  in addList (addList term1 term2) (addList term3 term4)

------------------------------------------------------------------------
-- VECTOR CONVERSION & EXPORTED KERNEL
------------------------------------------------------------------------

private
toVectExact : (k : Nat) -> List BoxInt -> Vect k BoxInt
toVectExact Z _ = []
toVectExact (S k) [] = intToBoxInt 0 :: toVectExact k []
toVectExact (S k) (x :: xs) = x :: toVectExact k xs

||| Recursive generation of the standard Spread Polynomials Sn(s) 
||| using Wildberger's strict algebraic triple-spread recurrence relation.
||| Returns a flat Vect (S n) BoxInt array of exact integer coefficients.
public export
generateSpreadPoly : (n : Nat) -> Vect (S n) BoxInt
generateSpreadPoly n = toVectExact (S n) (spreadList n)
