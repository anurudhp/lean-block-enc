import quantum

theorem adjoint_kron {m n p q : ℕ}(A : Matrix m n) (B : Matrix p q): (A ⊗ B)† = (A†) ⊗ (B†)
:= begin
    apply matrix.ext,
    intros j i,
    unfold kron,
    unfold Matrix.adjoint,
    simp,
end

theorem bra_dagger_eq_ket : ⟨0|† = |0⟩ := begin
  apply matrix.ext,
  intros i j,
  unfold Matrix.adjoint,
  unfold ket0 bra0,
  simp,
end
