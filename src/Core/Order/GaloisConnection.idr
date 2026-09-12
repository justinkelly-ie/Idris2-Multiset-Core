module Core.Order.GaloisConnection

import Core.Order.Preorder

%default total

--------------------------------------------------------------------------------
-- 1. GENERIC GALOIS CONNECTION INTERFACE (alpha -| gamma)
--------------------------------------------------------------------------------

||| Pure domain-agnostic Galois Adjunction between concrete poset `c` and abstract poset `a`.
||| Formalizes abstraction map alpha and concretization map gamma satisfying alpha -| gamma.
public export
interface (PreorderedMonoid concrete, PreorderedMonoid abstractDomain) => 
          GaloisConnection concrete abstractDomain where
  ||| Abstraction map alpha: C -> A
  alpha : concrete -> abstractDomain

  ||| Concretization map gamma: A -> C
  gamma : abstractDomain -> concrete

  ||| Monotonicity witness for alpha
  alphaMonotone : (x : concrete) -> (y : concrete) -> 
                  preorder x y = True -> preorder (alpha x) (alpha y) = True

  ||| Monotonicity witness for gamma
  gammaMonotone : (u : abstractDomain) -> (v : abstractDomain) -> 
                  preorder u v = True -> preorder (gamma u) (gamma v) = True

  ||| Adjunction identity witness: gamma (alpha x) >= x or gamma . alpha = id
  0 verifyAdjunctionIdentity : (x : concrete) -> gamma (alpha x) = x
