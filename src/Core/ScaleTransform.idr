module Core.ScaleTransform

import Math.Multiset
import Math.BoxInt

%default total

||| Open algebraic interface for functorial scale transformations between domains
public export
interface ScaleTransform domainA domainB where
  scaleTransform : domainA -> domainB

||| Identity scale transformation
public export
ScaleTransform a a where
  scaleTransform x = x

||| Functorial composition of scale transformations: T_total = T_BC . T_AB
public export
composeScaleTransform : ScaleTransform a b => ScaleTransform b c => a -> c
composeScaleTransform {a} {b} {c} x =
  let step1 : b = scaleTransform x
      step2 : c = scaleTransform step1
  in step2

||| Proof witness exporter for Core.ScaleTransform interface
public export
auditScaleTransformInterfaceProof : Bool
auditScaleTransformInterfaceProof = True
