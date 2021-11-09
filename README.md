# lean-qsvt-block-enc
Formalizing QSVT &amp; Block Encoding frameworks in LEAN

## Getting Started
First install Lean & Mathlib: [install instructions](https://leanprover-community.github.io/get_started.html). You might also want to get the VSCode plugin for Lean.

Use `leanpkg build` and `leanpkg test` to build and test respectively.

## Project
Currently I am not sure how I want to go about this. I'm just experimenting with a few different ways of representing reals and matrices, and will pick some convenient method.

The aim is to formalize the Block encoding and QSVT/QSP frameworks.

### Block encoding
Check reference [2]. The matrix is encoded in the top right block of a unitary, with some scaling, and up to some error. We then should formalize the various primitives they provide for working with these - products, linear combinations, functions etc.

### QSVT/QSP
Check ref [1]. QSVT is a framework to apply a function on the singular values of a matrix. QSP provides a way to implement arbitrary polynomial functions transforming the eigenvalues.
We must formalize these notions, and then use them to prove the various results in the field.

## References
1. [A Grand Unification of Quantum Algorithms](https://arxiv.org/abs/2105.02859)
1. [Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics](https://arxiv.org/abs/1806.01838) - formalism for block encoding