/-
Copyright 2021 Anurudh Peduri
Licensed under the Apache License, Version 2.0 (check LICENSE).

Authors: Anurudh Peduri
-/

import quantum
import algebra.group_power.basic
open Matrix

namespace BlockEncoding

@[simp]
noncomputable
def TopLeftBlock {s a : ℕ} (U : Op (s + a)) : Op s := begin
  let π := (|0⟩ ⊗ₙ a) ⊗ I 2^s,
  let π' := (⟨0| ⊗ₙ a) ⊗ I 2^s,
  simp at π π',
  rw ← pow_add at π π',
  rw ← add_comm at π π',
  exact (π' ⬝ U ⬝ π),
end

-- GSLW19, Definition 43
-- A is an s-qubit operator, U is an (α, a, ε)-block-encoding of A
def BlockEncoding {s : ℕ} (α : ℝ) (a : ℕ) (ε : ℝ) (A : Op s)
  := { U : Op (s + a) // U† ⬝ U = 1 ∧ ∥A - α • TopLeftBlock U ∥ ≤ ε }


lemma one_kron_one__one {a b : ℕ} : (I a) ⊗ (I b) = (I _) := begin 
  unfold kron,
  apply matrix.ext,
  intros i j,
  repeat { rw matrix.one_apply,},
  sorry,
end

lemma block_self {s : ℕ} (U : Op s) : @TopLeftBlock s 0 U = U := begin
  simp,
  unfold kron_n; simp,
  rw one_kron_one__one,
  sorry,
end

-- GSLW19, Definition 44
-- (Trivial block-encoding). A unitary matrix is a (1, 0, 0)-block-encoding of itself.
def TrivialEncoding {s : ℕ} (U : Op s) (h : unitary U) : BlockEncoding 1 0 0 U
  := ⟨U, ⟨h, by { rw block_self, simp }⟩⟩

-- GSLW19, Lemma 53
-- (Product of block-encoded matrices).
-- If U is an (α, a, δ)-block-encoding of an s-qubit operator A,
-- and V is an (β, b, ε)-block-encoding of an s-qubit operator B
-- then (I b ⊗ U)(I a ⊗ V) is an (αβ, a + b, αε + βδ)-block-encoding of AB.
def ProductEncoding {s a b : ℕ} {α δ β ε : ℝ} {A B : Op s}
  (U : BlockEncoding α a δ A)
  (V : BlockEncoding β b ε B)
  : BlockEncoding (α * β) (a + b) (α * ε + β * δ) (A ⬝ B) := sorry

end BlockEncoding

