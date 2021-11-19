# lean-qsvt-block-enc
Formalizing the Block Encoding framework in LEAN.

## Project
The aim is to formalize the Block Encoding framework in LEAN and possibly the QSVT/QSP frameworks.

### Block encoding
Check reference [1]. The matrix is encoded in the top right block of a unitary, with some scaling, and up to some error. We then should formalize the various primitives they provide for working with these - products, linear combinations, functions etc.

## Getting Started
First install Lean & Mathlib: [install instructions](https://leanprover-community.github.io/get_started.html).

Use `leanpkg build` and `leanpkg test` to build and test respectively.

## References
1. [Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics](https://arxiv.org/abs/1806.01838) - formalism for block encoding
1. [A Grand Unification of Quantum Algorithms](https://arxiv.org/abs/2105.02859)
1. [LEAN mathlib](https://leanprover-community.github.io/mathlib_docs/)

## Related Projects
1. [duckki/lean-quantum](https://github.com/duckki/lean-quantum) - basic formalism for QC in lean.
1. [Verified Quantum Computing](https://www.cs.umd.edu/~rrand/vqc/index.html) - in coq
