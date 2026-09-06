# Idris2-Multiset-Core

[![Idris 2 Verification](https://img.shields.io/badge/Idris_2-0.8.0-blue.svg)](https://www.idris-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Layer 1 Base Discrete Box Arithmetic & Rational Unixel Fractions for Idris 2**

`Idris2-Multiset-Core` provides foundational discrete mathematical primitives for the **10-Layer Constructive Multiset Physics Framework**:

- **`BoxInt`**: Type-refined signed integer counts wrapped in discrete boxes ($v \in \mathbb{Z}$) eliminating floating-point drift.
- **`Bit` Singletons**: Type-safe binary `Bit` constructors (`Zero` and `One`) with `boolToBit : Bool -> Bit` conversion functions.
- **`Multiset`**: Flat non-linear integer multiset containers mapping basis states to integer weights.
- **`Sing`**: Higher-order type-level singleton containers.

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`):

```bash
idris2 --build Idris2-Multiset-Core.ipkg
idris2 --install Idris2-Multiset-Core.ipkg
```

## 🔬 Architectural Principles

- **Total Constructivism**: Enforces `%default total` across all audit functions.
- **No Float Operations**: Strict integer/rational multiset arithmetic without continuous floating-point approximations.
- **QTT Linearity**: Linear comonoidal resource consumption via `LConsumable` and `LComonoid`.
