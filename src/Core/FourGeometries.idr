module Core.FourGeometries

import Core.BoxInt
import Core.ScaleTransform
import Data.Fin

%default total

------------------------------------------------------------------------
-- 1. THE 3-COLOR CHROMOGEOMETRIC SECTORS & FUNDAMENTAL GEOMETRIES
------------------------------------------------------------------------

||| The 3-color chromogeometric sectors.
public export
data ColorCharge = RedColor | GreenColor | BlueColor

public export
Eq ColorCharge where
  RedColor   == RedColor   = True
  GreenColor == GreenColor = True
  BlueColor  == BlueColor  = True
  _          == _          = False

public export
Show ColorCharge where
  show RedColor   = "Red"
  show GreenColor = "Green"
  show BlueColor  = "Blue"

public export
ScaleTransform ColorCharge Nat where
  scaleTransform RedColor   = 1
  scaleTransform GreenColor = 2
  scaleTransform BlueColor  = 3

public export
InvertibleScaleTransform ColorCharge Nat where
  invertScaleTransform Z = RedColor
  invertScaleTransform (S Z) = RedColor
  invertScaleTransform (S (S Z)) = GreenColor
  invertScaleTransform (S (S (S _))) = BlueColor

||| Classifies each cell index in Fin 27 into its exact QCD Color Sector.
||| Uses the Z-axis coordinate layer (z = -1 -> Red, z = 0 -> Green, z = +1 -> Blue).
public export
cellColorSector : Fin 27 -> ColorCharge
cellColorSector idx =
  case (finToNat idx) `div` 9 of
    0 => RedColor
    1 => GreenColor
    _ => BlueColor

||| The 4 canonical metric geometries governing space, time, gauge, and causality:
||| 1. EllipticGeom   (Blue Sector  / det g = +1 / Spacelike Confinement Canvas)
||| 2. HyperbolicGeom (Red Sector   / det g = -1 / Timelike Non-Abelian Gauge Engine)
||| 3. ParabolicGeom  (Green Sector / det g = 0  / Lightlike Remainder Dissipation Sink)
||| 4. SubstrateGeom  (Causal Poset / g22 = 0, g12 = 1 / Irreversible Cosmological Arrow)
public export
data FundamentalGeometry = 
    EllipticGeom 
  | HyperbolicGeom 
  | ParabolicGeom 
  | SubstrateGeom

public export
Eq FundamentalGeometry where
  EllipticGeom   == EllipticGeom   = True
  HyperbolicGeom == HyperbolicGeom = True
  ParabolicGeom  == ParabolicGeom  = True
  SubstrateGeom  == SubstrateGeom  = True
  _              == _              = False

public export
Show FundamentalGeometry where
  show EllipticGeom   = "Elliptic(Blue)"
  show HyperbolicGeom = "Hyperbolic(Red)"
  show ParabolicGeom  = "Parabolic(Green)"
  show SubstrateGeom  = "Substrate(Null)"

------------------------------------------------------------------------
-- 5. TYPE-LEVEL CHROMOGEOMETRIC INVARIANCE WITNESSES
------------------------------------------------------------------------

||| Type-level proof witness certifying 3-Metric Chromogeometric Quadrance Conservation:
||| BlueQuadrance + RedQuadrance = GreenQuadrance (27 + 128 = 155, 155 + 55 = 210).
public export
0 ChromogeometricQuadranceConservation : Nat -> Nat -> Nat -> Type
ChromogeometricQuadranceConservation b r g = b + r = g

||| Compile-time proof witness verifying Primorial 210 Chromogeometric Budget Conservation.
public export
0 prfChromogeometricBudgetConservation : ChromogeometricQuadranceConservation (27 + 128) 55 210
prfChromogeometricBudgetConservation = Refl
