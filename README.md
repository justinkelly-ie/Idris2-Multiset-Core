# Idris2-Multiset-Core

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 1 Base Discrete Box Arithmetic, Multisets & Galois Order Foundations for Idris 2**

`Idris2-Multiset-Core` forms **Layer 1** of the 10-layer constructive non-linear multiset science framework. It provides foundational discrete mathematical primitives, multiset monoids, linear QTT resource channels, scale transformation interfaces, and Galois connection posets—all built without continuous real numbers or floating-point approximations.

---

## 📦 Core Library Architecture & Modules

### 1. `Math.BoxInt`
- **Dirac Cancellation Normalization:** Signed Box Integer arithmetic (`BoxInt = Multiset Integer SignedUnit`) operating over `Pos` and `Neg` signed units with mutual annihilation.
- **Monomorphic Arithmetic:** Provides `addBox`, `subBox`, `multBox`, `absBox`, `boxToNat`, and `natToBox` monomorphic integer functions that eliminate typeclass method blocking during compile-time `%macro` reflection.
- **Zero-Defect Bounds:** Exact integer counting ($v \in \mathbb{Z}$) preventing numerical drift.

### 2. `Math.Multiset`
- **Free Commutative Monoids:** Inductive `Box` multiset container (`Box token`) tracking exact integer token multiplicities.
- **Algebraic Operations:** Key-value lookup (`lookupBox`), insertion (`insertBox`), multiset union (`unionBox`), scalar scaling (`scaleBox`), difference (`diffBox`), and multiset zero-cancellation (`canonicalizeBox`).
- **Monoid Laws:** Verified associativity, identity, and commutativity laws over multiset union (`++`).

### 3. `Math.LMultiset`
- **Linear Resource Channels:** Quantitative Type Theory (QTT) linear multiset resource channels (`LMultiset`).
- **Comonoidal Interfaces:** Typeclass contracts `LConsumable` and `LComonoid` enforcing strict linear resource conservation (multiplicity 1) at compile time.

### 4. `Math.DepMultiset` & Singletons
- **`Math.DepMultiset`:** Dependent multiset specifications and type-indexed multisets (`DepMultiset`).
- **`Math.Singleton.Bit`:** Type-safe binary `Bit` singletons (`Zero` and `One`) with `boolToBit : Bool -> Bit` conversion functions.
- **`Math.Singleton.Sing`:** Higher-order type-level singleton containers (`Sing`).
- **`Math.Spread` & `Math.Interfaces`:** Discrete spread/quadrance operations and core mathematical interfaces.

### 5. `Core.ScaleTransform`
- **Functorial Scale Interfaces:** Open algebraic interfaces `ScaleTransform domainA domainB` and bidirectional `InvertibleScaleTransform domainA domainB`.
- **Pipeline Composition:** Scale pipeline composition (`composeScaleTransform`, `composeInvertibleScaleTransform`) establishing scale-invariant mapping across physical domains.

### 6. `Core.Order.Preorder` & `Core.Order.GaloisConnection`
- **Preordered Monoids:** Poset structure (`PreorderedMonoid`) parameterizing state spaces with monotonic preorder bounds.
- **Galois Adjunction Duality ($f_* \dashv f^*$):** Generic domain-agnostic Galois connection interface (`GaloisConnection concrete abstractDomain`) formalizing abstraction ($\alpha: C \to A$) and concretization ($\gamma: A \to C$) maps with verified monotonicity and adjunction identity witnesses.

---

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`):

```bash
idris2 --build Idris2-Multiset-Core.ipkg
idris2 --install Idris2-Multiset-Core.ipkg
```

---

## 🔬 Architectural Principles

- **Total Constructivism:** Enforces `%default total` across all library functions.
- **Zero Floating-Point Drift:** Strict integer and exact rational multiset arithmetic without continuous real-number approximations.
- **QTT Linearity:** Linear resource accounting preventing illegal copying or deletion of physical quanta.
- **Elaborator Reduction:** Monomorphic arithmetic routines avoiding typeclass interface method blocking during macro reflection.
