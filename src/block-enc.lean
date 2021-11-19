/-
Copyright 2021 Anurudh Peduri
Licensed under the Apache License, Version 2.0 (check LICENSE).

Authors: Anurudh Peduri
-/

import quantum

namespace BlockEncoding

lemma pow2_mul (a b : ℕ) : 2 ^ b * 2 ^ a = 2 ^ (a + b) := sorry

@[simp]
def TopLeftBlock {s a : ℕ} (U : Op (s + a)) : Op s := begin
  let π := |0⟩ ⊗ₙ a ⊗ (I 2) ⊗ₙ s,
  let π' := (⟨0| ⊗ₙ a) ⊗ ((I 2) ⊗ₙ s),
  simp at π π',
  rw pow2_mul at π,
  rw pow2_mul at π',
  exact (π' ⬝ U ⬝ π),
end

lemma kron_0 {m n : ℕ} {A : Matrix m n} : A ⊗ₙ 0 = (1 : Matrix 1 1) := begin
  unfold kron_n,
  simp,
  apply matrix.ext,
  intros,
  fin_cases i,
  fin_cases j,
  refl,
end

lemma kron_I {m n : ℕ} : (I m) ⊗ₙ n = I (m ^ n) := begin
  unfold kron_n,
  simp,
  apply matrix.ext,
  intros,
  induction n with n H, {
    simp,
    fin_cases i,
    fin_cases j,
    refl,
  }, {
    sorry,
  }
end

lemma one_times_one {m n : ℕ} : (I m) ⊗ (I n) = 1 := begin
  unfold kron,
  apply matrix.ext,
  intros,
  repeat { rw matrix.one_apply },
  simp,
  cases (fin.decidable_eq _ i j), {
    sorry,
  }, {
    rw h,
    simp,
  }
end

-- GSLW19, Definition ??
-- U is an (α, a, ε)-block-encoding of A
def BlockEncoding {s : ℕ} (α : ℝ) (a : ℕ) (ε : ℝ) (A : Op s)
  := { U : Op (s + a) // A - (α : ℂ) • TopLeftBlock U = 0 }

def TrivialEncoding {s : ℕ} (A : Op s) (H: Matrix.unitary A) : BlockEncoding 1 0 0 A := ⟨A, begin
  simp,

  repeat { rewrite kron_0, },
  repeat { rewrite kron_I, },
  rewrite one_times_one,
  unfold cast,
  -- rw matrix.one_mul A,
  sorry,
end⟩ 

end BlockEncoding

