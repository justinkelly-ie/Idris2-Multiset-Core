# 📦 Idris2-Multiset-Core

**Base Discrete Box Arithmetic & Rational Unixel Fractions for Idris 2**

`Idris2-Multiset-Core` provides the core discrete mathematical primitives for the **Constructive Multiset Physics Framework**:
- `BoxInt`: Signed integer counts wrapped in discrete boxes ($v \in \mathbb{Z}$).
- `UnixelFraction`: Exact rational fractions ($p/q \in \mathbb{Q}_{>0}$) with cross-multiplication equivalence (`rationalEquiv`).
- `Box a`: Balanced binary multiset trees mapping key states to integer counts.

---

## 🚀 Building & Installing

Built with Idris 2 (`0.8.0`):

```bash
idris2 --build Idris2-Multiset-Core.ipkg
idris2 --install Idris2-Multiset-Core.ipkg
```

---

## 🔬 Language & Framework Integration

Written in **Idris 2** enforcing total constructivism (`%default total`).
