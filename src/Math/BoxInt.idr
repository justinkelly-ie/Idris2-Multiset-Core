module Math.BoxInt

import Data.Linear
import Math.Interfaces
import public Math.Multiset
import public Core.BoxInt

%default total

public export
data SignedUnit : Type where
  Pos : SignedUnit
  Neg : SignedUnit

public export
Eq SignedUnit where
  Pos == Pos = True
  Neg == Neg = True
  _ == _ = False

public export
Show SignedUnit where
  show Pos = "+"
  show Neg = "-"

public export
Semigroup SignedUnit where
  (<+>) Pos Pos = Pos
  (<+>) Pos Neg = Neg
  (<+>) Neg Pos = Neg
  (<+>) Neg Neg = Pos

public export
Monoid SignedUnit where
  neutral = Pos

||| A Box Arithmetic Multiset Integer Representation
public export
MultisetBoxInt : Type
MultisetBoxInt = Multiset Integer SignedUnit

||| Normalizes a MultisetBoxInt by mutually annihilating Pos and Neg (Dirac Cancellation).
public export
normalizeBoxInt : MultisetBoxInt -> MultisetBoxInt
normalizeBoxInt xs =

  let rle = multisetToList xs
      posCount = foldl (\acc, (u, val) => if u == Pos then acc + val else acc) 0 rle
      negCount = foldl (\acc, (u, val) => if u == Neg then acc + val else acc) 0 rle
      totalVal = posCount - negCount
  in if totalVal == 0 then ZeroM
     else if totalVal > 0 then AddM Pos totalVal ZeroM
     else AddM Neg (-totalVal) ZeroM

||| Safely and linearly unwraps a MultisetBoxInt into an unrestricted Integer.
public export
boxToInt : (1 _ : MultisetBoxInt) -> Ur Integer
boxToInt ZeroM = MkUr 0
boxToInt (AddM Pos c xs) =
  let (MkUr n) = boxToInt xs
  in MkUr (c + n)
boxToInt (AddM Neg c xs) =
  let (MkUr n) = boxToInt xs
  in MkUr (-c + n)

||| Creates a MultisetBoxInt from an Integer.
public export
intToMultisetBoxInt : Integer -> MultisetBoxInt
intToMultisetBoxInt n = 
  if n == 0 then ZeroM
  else if n > 0 then AddM Pos n ZeroM
  else AddM Neg (-n) ZeroM

||| Creates a MultisetBoxInt from a Nat count multiset.
public export
natToMultisetBoxInt : Nat -> MultisetBoxInt
natToMultisetBoxInt n = intToMultisetBoxInt (cast n)

||| Negates a MultisetBoxInt.
public export
boxNegate : MultisetBoxInt -> MultisetBoxInt
boxNegate ZeroM = ZeroM
boxNegate (AddM Pos c xs) = AddM Neg c (boxNegate xs)
boxNegate (AddM Neg c xs) = AddM Pos c (boxNegate xs)

public export
mulSignedUnit : SignedUnit -> SignedUnit -> SignedUnit
mulSignedUnit Pos Pos = Pos
mulSignedUnit Pos Neg = Neg
mulSignedUnit Neg Pos = Neg
mulSignedUnit Neg Neg = Pos

||| Adds two BoxInts.
%inline public export
boxAdd : BoxInt -> BoxInt -> BoxInt
boxAdd = addBox

||| Subtracts two BoxInts.
%inline public export
boxSub : BoxInt -> BoxInt -> BoxInt
boxSub = subBox

||| Multiplies two BoxInts.
%inline public export
boxMult : BoxInt -> BoxInt -> BoxInt
boxMult (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)

||| Multiplies two MultisetBoxInts via structural Applicative tensor product over SignedUnit group.
public export
multisetBoxMult : MultisetBoxInt -> MultisetBoxInt -> MultisetBoxInt
multisetBoxMult xs ys = normalizeBoxInt [| mulSignedUnit xs ys |]


||| Returns the absolute value of a MultisetBoxInt.
public export
multisetBoxAbs : MultisetBoxInt -> MultisetBoxInt
multisetBoxAbs xs =
  let normalized = normalizeBoxInt xs
  in case normalized of
       AddM Neg c rest => AddM Pos c rest
       other => other

||| Discrete ceiling log2 directly over MultisetBoxInt.
public export
multisetBoxLog2 : MultisetBoxInt -> MultisetBoxInt
multisetBoxLog2 xs =
  let (MkUr val) = boxToInt (multisetBoxAbs xs)
  in intToMultisetBoxInt (calcLog2 val)
  where
    calcLog2 : Integer -> Integer
    calcLog2 n =
      if n <= 1 then 0
      else 1 + assert_total (calcLog2 (div n 2))

-----------------------------------------------------------------------
-- LINEAR INSTANCES FOR MULTISETBOXINT
-----------------------------------------------------------------------

public export
implementation LConsumable MultisetBoxInt where
  lconsume = consumeMultiset

public export
implementation LComonoid MultisetBoxInt where
  lcomult ZeroM = Builtin.(#) ZeroM ZeroM
  lcomult (AddM u c rest) =
    let Builtin.(#) r1 r2 = lcomult rest
    in Builtin.(#) (AddM u c r1) (AddM u c r2)

public export
implementation LEq MultisetBoxInt where
  lEq ZeroM ZeroM = Builtin.(#) True (Builtin.(#) ZeroM ZeroM)
  lEq (AddM u1 c1 r1) (AddM u2 c2 r2) =
    let Builtin.(#) subRes (Builtin.(#) r1' r2') = lEq r1 r2
        eqUnits = u1 == u2 && c1 == c2 && subRes
    in Builtin.(#) eqUnits (Builtin.(#) (AddM u1 c1 r1') (AddM u2 c2 r2'))
  lEq x y = Builtin.(#) False (Builtin.(#) x y)


-----------------------------------------------------------------------
-- TYPE-REFINED NON-ZERO BOXINT
-----------------------------------------------------------------------

public export
record NonZeroBoxInt where
  constructor MkNonZeroBoxInt
  val : BoxInt

public export
toNonZeroBoxInt : BoxInt -> Maybe NonZeroBoxInt
toNonZeroBoxInt b =
  let n = unwrapBox b
  in if n == 0 then Nothing
     else Just (MkNonZeroBoxInt b)

