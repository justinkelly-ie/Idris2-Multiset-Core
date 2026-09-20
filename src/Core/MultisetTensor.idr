module Core.MultisetTensor

import public Core.BoxInt
import public Math.Multiset
import Math.OnSeq.FusedStream
import Data.List

%default total

||| An Adjoint Multiset Tensor V ⊗ W* represented as a 2D pair multiset.
||| This replaces rigid grid matrix containers with an emergent, deforested multiset structure.
public export
MultisetTensor : Type -> Type -> Type
MultisetTensor a b = Multiset BoxInt (a, b)

||| Tensor Outer Product (A ⊗ B):
||| Computes the tensor product of two multiset state vectors.
public export
tensorProduct : Multiset BoxInt a -> Multiset BoxInt b -> MultisetTensor a b
tensorProduct ZeroM _ = ZeroM
tensorProduct (AddM x w1 restX) ys =
  addMultiset (scaleRow x w1 ys) (tensorProduct restX ys)
  where
    scaleRow : a -> BoxInt -> Multiset BoxInt b -> MultisetTensor a b
    scaleRow _ _ ZeroM = ZeroM
    scaleRow itemA weightA (AddM itemB weightB restY) =
      AddM (itemA, itemB) (weightA * weightB) (scaleRow itemA weightA restY)

||| Transposes an Adjoint Multiset Tensor (A^T): (a, b) -> (b, a).
public export
transposeTensor : MultisetTensor a b -> MultisetTensor b a
transposeTensor ZeroM = ZeroM
transposeTensor (AddM (x, y) w rest) = AddM (y, x) w (transposeTensor rest)

||| Stream Hylomorphic Tensor Contraction (Matrix Multiplication A · B):
||| Multiplies two multiset tensors A : (a, b) and B : (b, c) -> (a, c).
public export
multisetTensorMult : Eq b => MultisetTensor a b -> MultisetTensor b c -> MultisetTensor a c
multisetTensorMult ZeroM _ = ZeroM
multisetTensorMult (AddM (i, k1) w1 restA) tensorB =
  let contracted = matchRow i k1 w1 tensorB
  in addMultiset contracted (multisetTensorMult restA tensorB)
  where
    matchRow : a -> b -> BoxInt -> MultisetTensor b c -> MultisetTensor a c
    matchRow _ _ _ ZeroM = ZeroM
    matchRow itemI targetK weight1 (AddM (k2, j) weight2 restB) =
      if targetK == k2
        then AddM (itemI, j) (weight1 * weight2) (matchRow itemI targetK weight1 restB)
        else matchRow itemI targetK weight1 restB

||| Monomorphic 2D Determinant over MultisetTensor: det([a b; c d]) = a*d - b*c
%inline public export
detTensor2D : BoxInt -> BoxInt -> BoxInt -> BoxInt -> BoxInt
detTensor2D a b c d = subBox (a * d) (b * c)

||| Monomorphic 2D Trace over MultisetTensor: tr([a b; c d]) = a + d
%inline public export
traceTensor2D : BoxInt -> BoxInt -> BoxInt
traceTensor2D a d = addBox a d

------------------------------------------------------------------------
-- GALOIS 4GEOMETRIES PUSHFORWARD STREAMS (f_* ⊣ f^*)
------------------------------------------------------------------------

||| Galois Fiber Pushforward (f_*) computing exact chromogeometric quadrance
||| Q(v) = v^T * g_Sector * v directly over multiset tensor streams.
public export
chromometricQuadrance : GeometrySector -> BoxInt -> BoxInt -> BoxInt -> BoxInt
chromometricQuadrance Elliptic   dx dy dz = addBox (addBox (dx * dx) (dy * dy)) (addBox (dz * dz) 1)
chromometricQuadrance Hyperbolic dx dy dz = addBox (subBox (addBox (dx * dx) (dy * dy)) (dz * dz)) 1
chromometricQuadrance Parabolic  dx dy dz = addBox (addBox (dx * dx) (dy * dy)) 1
chromometricQuadrance Substrate  _  _  _  = 1
