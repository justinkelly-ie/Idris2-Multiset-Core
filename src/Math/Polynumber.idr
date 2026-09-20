module Math.Polynumber

import Data.Linear
import Math.Interfaces


%default total

-----------------------------------------------------------------------
-- 1. METRICAL CONSTRAINTS
-----------------------------------------------------------------------

||| Defines whether a metric space has open orthogonal directions.
public export
data Flexibility : Type where
  Rigid : Flexibility
  Foldable : (degreesOfFreedom : Nat) -> Flexibility

||| The metrical structure defining the space in which a multiset evaluates.
public export
record Geometry where
  constructor MkGeometry
  dimensions  : Nat
  flexibility : Flexibility


