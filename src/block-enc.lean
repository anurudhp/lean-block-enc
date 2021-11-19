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
def TopLeftBlock {s a : ℕ} (U : Op (a + s)) : Op s := begin
  let π := (|0⟩ ⊗ₙ a) ⊗ I 2^s,
  let π' := (⟨0| ⊗ₙ a) ⊗ I 2^s,
  simp at π π',
  rw ← pow_add at π,
  rw ← pow_add at π',
  exact (π' ⬝ U ⬝ π),
end

-- GSLW19, Definition 43
-- A is an s-qubit operator, U is an (α, a, ε)-block-encoding of A
def BlockEncoding {s : ℕ} (α : ℝ) (a : ℕ) (ε : ℝ) (A : Op s)
  := { U : Op (a + s) // U† ⬝ U = 1 ∧ ∥A - α•TopLeftBlock U ∥ ≤ ε }

def TrivialEncoding {s : ℕ} (A : Op s) (H: Matrix.unitary A) : BlockEncoding 1 0 0 A := ⟨A, sorry⟩

end BlockEncoding

