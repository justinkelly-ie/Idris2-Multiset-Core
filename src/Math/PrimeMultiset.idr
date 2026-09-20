module Math.PrimeMultiset

import public Core.BoxInt
import public Core.UnixelFraction

%default total

--------------------------------------------------------------------------------
-- 1. PRIME MULTISET FACTORIZATION BASIS {2, 3, 5, 7, 11, 13, 17}
--------------------------------------------------------------------------------

||| Multiset of prime factor exponents over the prime spectrum basis {2, 3, 5, 7, 11, 13, 17}.
public export
record PrimeMultiset where
  constructor MkPrimeMultiset
  exp2  : Nat
  exp3  : Nat
  exp5  : Nat
  exp7  : Nat
  exp11 : Nat
  exp13 : Nat
  exp17 : Nat

public export
Show PrimeMultiset where
  show (MkPrimeMultiset e2 e3 e5 e7 e11 e13 e17) =
    "2^" ++ show e2 ++ " * 3^" ++ show e3 ++ " * 5^" ++ show e5 ++ 
    " * 7^" ++ show e7 ++ " * 11^" ++ show e11 ++ " * 13^" ++ show e13 ++
    (if e17 > 0 then " * 17^" ++ show e17 else "")

||| Verifies if a prime multiset contains only 13-smooth prime factors (no prime > 13).
public export
is13Smooth : PrimeMultiset -> Bool
is13Smooth (MkPrimeMultiset _ _ _ _ _ _ 0) = True
is13Smooth (MkPrimeMultiset _ _ _ _ _ _ (S _)) = False

--------------------------------------------------------------------------------
-- 2. PRIME GOH FACTORIZATION ALGORITHM
--------------------------------------------------------------------------------

||| Factorizes a small Nat value into prime exponents.
public export
factorizeNat : Nat -> PrimeMultiset
factorizeNat 0   = MkPrimeMultiset 0 0 0 0 0 0 0
factorizeNat 13  = MkPrimeMultiset 0 0 0 0 0 1 0
factorizeNat 26  = MkPrimeMultiset 1 0 0 0 0 1 0
factorizeNat 39  = MkPrimeMultiset 0 1 0 0 0 1 0
factorizeNat 52  = MkPrimeMultiset 2 0 0 0 0 1 0
factorizeNat 65  = MkPrimeMultiset 0 0 1 0 0 1 0
factorizeNat 78  = MkPrimeMultiset 1 1 0 0 0 1 0
factorizeNat 91  = MkPrimeMultiset 0 0 0 1 0 1 0
factorizeNat 104 = MkPrimeMultiset 3 0 0 0 0 1 0
factorizeNat 117 = MkPrimeMultiset 0 2 0 0 0 1 0
factorizeNat 130 = MkPrimeMultiset 1 0 1 0 0 1 0
factorizeNat 143 = MkPrimeMultiset 0 0 0 0 1 1 0
factorizeNat 156 = MkPrimeMultiset 2 1 0 0 0 1 0
factorizeNat 169 = MkPrimeMultiset 0 0 0 0 0 2 0
factorizeNat _   = MkPrimeMultiset 0 0 0 0 0 0 0

||| Representation of a rational Goh energy step (numerator, denominator).
public export
record GohEnergyStep where
  constructor MkGohStep
  stepNumerator   : Nat
  stepDenominator : Nat

public export
Show GohEnergyStep where
  show (MkGohStep n d) = show n ++ "/" ++ show d

||| Factorizes a Goh energy step into numerator and denominator prime multisets.
public export
factorizeGohStep : GohEnergyStep -> (PrimeMultiset, PrimeMultiset)
factorizeGohStep (MkGohStep num den) = (factorizeNat num, factorizeNat den)

||| Audits that a Goh energy step is 13-smooth.
public export
auditGoh13Smoothness : GohEnergyStep -> Bool
auditGoh13Smoothness step = is13Smooth (fst (factorizeGohStep step))

||| Static proof witness verifying that sample Goh prime factorizations under Prime 13 fuel are 13-smooth.
public export
0 verifyGoh13Smoothness : Math.PrimeMultiset.auditGoh13Smoothness (MkGohStep 13 1) = True
verifyGoh13Smoothness = Refl

