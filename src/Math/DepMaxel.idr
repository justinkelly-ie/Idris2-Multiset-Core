module Math.DepMaxel

import Math.Multiset
import Math.DepMultiset
import public Math.Pixel

%default covering

||| A dependently typed Maxel is a DepMultiset of Pixels.
public export
0 DepMaxel : (metric : Metric) -> (c : Type) -> (a : Type) -> (contents : Multiset c (Pixel metric a)) -> Type
DepMaxel metric c a contents = DepMultiset c (Pixel metric a) contents
