module Math.BoxInt

import Data.Linear
import Math.Interfaces
import public Math.Multiset

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

||| A Box Arithmetic Linear Integer (BoxInt)
public export
BoxInt : Type
BoxInt = Multiset Integer SignedUnit

||| Normalizes a BoxInt by mutually annihilating Pos and Neg (Dirac Cancellation).
public export
normalizeBoxInt : BoxInt -> BoxInt
normalizeBoxInt xs =
  let rle = multisetToList xs
      posCount = foldl (\acc, (u, val) => if u == Pos then acc + val else acc) 0 rle
      negCount = foldl (\acc, (u, val) => if u == Neg then acc + val else acc) 0 rle
      totalVal = posCount - negCount
  in if totalVal == 0 then ZeroM
     else if totalVal > 0 then AddM Pos totalVal ZeroM
     else AddM Neg (-totalVal) ZeroM

||| Safely and linearly unwraps a BoxInt into an unrestricted Integer.
public export
boxToInt : (1 _ : BoxInt) -> Ur Integer
boxToInt ZeroM = MkUr 0
boxToInt (AddM Pos c xs) = 
  let (MkUr n) = boxToInt xs 
  in MkUr (c + n)
boxToInt (AddM Neg c xs) = 
  let (MkUr n) = boxToInt xs 
  in MkUr (-c + n)

||| Creates a BoxInt from an Integer.
public export
intToBoxInt : Integer -> BoxInt
intToBoxInt n = 
  if n == 0 then ZeroM
  else if n > 0 then AddM Pos n ZeroM
  else AddM Neg (-n) ZeroM

||| Creates a BoxInt from a Nat count multiset.
public export
natToBoxInt : Nat -> BoxInt
natToBoxInt n = intToBoxInt (cast n)

||| Negates a BoxInt.
public export
boxNegate : BoxInt -> BoxInt
boxNegate ZeroM = ZeroM
boxNegate (AddM Pos c xs) = AddM Neg c (boxNegate xs)
boxNegate (AddM Neg c xs) = AddM Pos c (boxNegate xs)

||| Adds two BoxInts.
public export
boxAdd : BoxInt -> BoxInt -> BoxInt
boxAdd xs ys = normalizeBoxInt (addMultiset xs ys)

||| Subtracts two BoxInts.
public export
boxSub : BoxInt -> BoxInt -> BoxInt
boxSub xs ys = boxAdd xs (boxNegate ys)

||| Multiplies two BoxInts.
public export
boxMult : BoxInt -> BoxInt -> BoxInt
boxMult xs ys =
  let (MkUr xVal) = boxToInt xs
      (MkUr yVal) = boxToInt ys
  in intToBoxInt (xVal * yVal)

public export
Num BoxInt where
  (+) = boxAdd
  (*) = boxMult
  fromInteger n = intToBoxInt n

public export
Neg BoxInt where
  negate = boxNegate
  (-) = boxSub

public export
Ord BoxInt where
  compare xs ys =
    let (MkUr x) = boxToInt xs
        (MkUr y) = boxToInt ys
    in compare x y

||| Returns the absolute value of a BoxInt.
public export
boxAbs : BoxInt -> BoxInt
boxAbs xs =
  let normalized = normalizeBoxInt xs
  in case normalized of
       AddM Neg c rest => AddM Pos c rest
       other => other

public export
Abs BoxInt where
  abs = boxAbs

-----------------------------------------------------------------------
-- LINEAR INSTANCES
-----------------------------------------------------------------------

public export
implementation LConsumable BoxInt where
  lconsume = consumeMultiset

public export
implementation LComonoid BoxInt where
  lcomult ZeroM = Builtin.(#) ZeroM ZeroM
  lcomult (AddM u c rest) =
    let Builtin.(#) r1 r2 = lcomult rest
    in Builtin.(#) (AddM u c r1) (AddM u c r2)

public export
implementation LEq BoxInt where
  lEq ZeroM ZeroM = Builtin.(#) True (Builtin.(#) ZeroM ZeroM)
  lEq (AddM u1 c1 r1) (AddM u2 c2 r2) =
    let Builtin.(#) subRes (Builtin.(#) r1' r2') = lEq r1 r2
        headMatch = (u1 == u2) && (c1 == c2)
        finalRes = if headMatch then subRes else case lconsume subRes of () => False
    in Builtin.(#) finalRes (Builtin.(#) (AddM u1 c1 r1') (AddM u2 c2 r2'))
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
  let (MkUr n) = boxToInt b
  in if n == 0 then Nothing
     else Just (MkNonZeroBoxInt b)
