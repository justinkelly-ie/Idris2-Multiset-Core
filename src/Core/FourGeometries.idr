module Core.FourGeometries

import Core.BoxInt

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
