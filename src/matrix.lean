/-
Copyright 2021 Anurudh Peduri 
Licensed under the Apache License, Version 2.0 (check LICENSE).

Authors: Anurudh Peduri 
Some parts borrowed from https://github.com/duckki/lean-quantum/
-/

import data.complex.basic
import data.complex.is_R_or_C
import algebra.star.basic
import data.matrix.basic
import analysis.complex.basic
import analysis.normed_space.basic
open_locale complex_conjugate

------------------------------------------------------------------------------
-- Convenience definition for real/complex numbers

notation |x| := is_R_or_C.abs x

------------------------------------------------------------------------------
-- Convenience definitions for complex matrix

@[reducible]
def Matrix (m n : ℕ) := matrix (fin m) (fin n) ℂ

namespace Matrix

variables {m n : ℕ}

-- Definition of `adjoint` or `†` (dagger) operator.
@[simp]
def adjoint (M : Matrix m n) : Matrix n m | x y := conj (M y x)

noncomputable
instance spectral_norm_group : normed_group (Matrix m n) := matrix.normed_group
noncomputable
instance spectral_norm_space : normed_space ℂ (Matrix m n) := matrix.normed_space

end Matrix

notation `Vector` n := Matrix n 1
notation `RVector` n := Matrix 1 n
notation `Square` n := Matrix n n
notation `I` n := (1 : Matrix n n)

infixl `⬝`:80 := matrix.mul
postfix `†`:100 := Matrix.adjoint


------------------------------------------------------------------------------
-- Vector properties

namespace Matrix

variables {n : ℕ} (s : Vector n)

-- The property of "unit" Vectors.
def unit := s† ⬝ s = 1

end Matrix


------------------------------------------------------------------------------
-- Square matrix properties

namespace Matrix

variables {n : ℕ} (M : Square n)

def normal := M† ⬝ M = M ⬝ M†

def unitary := M† ⬝ M = 1

def hermitian := M† = M

def projector := M ⬝ M = M

end Matrix


------------------------------------------------------------------------------
-- Standard basis `std_basis` for a column vector with a single value
section std_basis

variables {m : Type*} [fintype m]
variables [decidable_eq m]

-- column vector with a single value at a given row
@[simp]
def std_basis (i : m) : matrix m (fin 1) ℂ
:= λ j _, if j = i then 1 else 0

end std_basis


------------------------------------------------------------------------------
-- Kronecker product definition

section kron

variables {m n p q : ℕ}

-- kron_div: `i / p` : `fin m`
@[reducible]
def kron_div (i : fin (m*p)) : fin m := ⟨ (i : ℕ)/p, sorry⟩

-- kron_mod: `i % p` : `fin p`
@[reducible]
def kron_mod (i : fin (m*p)) : fin p := ⟨(i : ℕ)%p, sorry⟩

-- Kronecker product
def kron (A : Matrix m n) (B : Matrix p q) : Matrix (m*p) (n*q)
:= λ i j,   -- A (i/p) (j/q) * B (i%p) (j%q)
      A (kron_div i) (kron_div j)
    * B (kron_mod i) (kron_mod j)

-- kron_loc: `m * r + v : fin (m * p)
-- Reverses `(r, v)` back to `x`, where `r = kron_div x` and `v = kron_mod x`.
@[reducible]
def kron_loc (r : fin m) (v : fin p) : fin (m * p) :=
  ⟨p * (r : ℕ) + (v : ℕ), sorry⟩

def kron_n : Π (A : Matrix p q) (n : ℕ), Matrix (p^n) (q^n) := begin
  intros,
  cases n,
  simp,
  exact (I 1),
  induction n with n A', {
    simp,
    exact A,
  }, {
    exact (kron A A'),
  }
end

end kron

infixl ` ⊗ `:75 := kron
infixl ` ⊗ₙ `:76 := kron_n

