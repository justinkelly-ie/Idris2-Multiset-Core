module Math.BoxNat

import Data.Linear
import Math.Interfaces
import public Math.Multiset

||| A Box Arithmetic Natural Multiset (BoxNat)
||| Parameterized over discrete Nat counts with unit element ()
public export
BoxNat : Type
BoxNat = Multiset Nat ()

||| Computes the total Nat tally of a BoxNat.
public export
boxNatToNat : BoxNat -> Nat
boxNatToNat ZeroM = 0
boxNatToNat (AddM () c xs) = c + boxNatToNat xs

||| Creates a BoxNat from a Nat.
public export
natToBoxNat : Nat -> BoxNat
natToBoxNat Z = ZeroM
natToBoxNat n = AddM () n ZeroM

||| Adds two BoxNat multisets (lazy structural merge).
public export
boxNatAdd : BoxNat -> BoxNat -> BoxNat
boxNatAdd xs ys = addMultiset xs ys

||| Normalizes a BoxNat by coalescing duplicate () counts into a single RLE node.
public export
normalizeBoxNat : BoxNat -> BoxNat
normalizeBoxNat xs =
  let totalCount = boxNatToNat xs
  in natToBoxNat totalCount

public export
Eq BoxNat where
  xs == ys = boxNatToNat xs == boxNatToNat ys

public export
Ord BoxNat where
  compare xs ys = compare (boxNatToNat xs) (boxNatToNat ys)

public export
Show BoxNat where
  show xs = "BoxNat(" ++ show (boxNatToNat xs) ++ ")"

-----------------------------------------------------------------------
-- LINEAR INSTANCES
-----------------------------------------------------------------------

||| Linear BoxNat Consumption
public export
implementation LConsumable BoxNat where
  lconsume = consumeMultiset

||| Linear BoxNat Duplication
public export
implementation LComonoid BoxNat where
  lcomult ZeroM = Builtin.(#) ZeroM ZeroM
  lcomult (AddM () c rest) =
    let Builtin.(#) r1 r2 = lcomult rest
    in Builtin.(#) (AddM () c r1) (AddM () c r2)
