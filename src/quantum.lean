/-
Copyright 2021 Anurudh Peduri
Licensed under the Apache License, Version 2.0 (check LICENSE).

Authors: Anurudh Peduri
Some parts borrowed from https://github.com/duckki/lean-quantum/
-/

import matrix
import data.matrix.notation

open_locale big_operators
open Matrix

------------------------------------------------------------------------------
-- Quantum Definitions

abbreviation Ket (n : ℕ) := Vector (2^n)
abbreviation Bra (n : ℕ) := RVector (2^n)
abbreviation Op (n : ℕ) := Square (2^n)

------------------------------------------------------------------------------
-- Matrix helpers for measurement definitions

namespace Matrix

variables {n m : ℕ} (s : Vector n)

/-- Projection operator onto the state `s` (aka "observable").
`proj s` can be read as `|ψ⟩⟨ψ|`, when `|ψ⟩ = s`. -/
def proj : Square n := s ⬝ (s†)

/-- Trace of square matrix -/
def trace (A : Square n) : ℂ := ∑ i, A i i

notation `Tr(` x `)` := trace x

/-- `n × n` partial traces of `m × m` subcomponents of
`(n * m) × (n * m)` square matrix. -/
def partial_trace (M : Square (n * m)) : Square n
:= λ i j, ∑ k, M (kron_loc i k) (kron_loc j k)

notation `Tr'(` x `)` := partial_trace x

end Matrix

namespace Matrix
end Matrix

------------------------------------------------------------------------------
-- Common states
notation `√2` := real.sqrt 2
notation `ι` := complex.I

-- |0⟩ and |1⟩ using `std_basis`
def ket0 : Ket 1 := ![![1], ![0]]
def ket1 : Ket 1 := ![![0], ![1]]
def bra0 : Bra 1 := ket0†
def bra1 : Bra 1 := ket1†

-- hadamard basis
noncomputable def ketplus : Ket 1 := ![![1/√2], ![1/√2]]
noncomputable def ketminus : Ket 1 := ![![1/√2], ![-1/√2]]
noncomputable def braplus : Bra 1 := ketplus†
noncomputable def braminus : Bra 1 := ketminus†

notation `|0⟩` := ket0
notation `|1⟩` := ket1
notation `⟨0|` := bra0
notation `⟨1|` := bra1
notation `|+⟩` := ketplus
notation `|-⟩` := ketminus
notation `⟨+|` := braplus
notation `⟨-|` := braminus

-- |00...0⟩ (= |0⟩ ⊗ ... ⊗ |0⟩ or the `n`-th tensor power of |0⟩).
-- Used for zero padding or ancillae qubits.
def ket_zeros (n : ℕ) : Ket n := std_basis ⟨0, by simp⟩

------------------------------------------------------------------------------
-- Common single qubit unitaries

-- X gate (aka NOT gate)
def σX : Op 1 := ![
    ![ 0, 1 ],
    ![ 1, 0 ]]

def σY : Op 1 := ![
    ![ 0, ι ],
    ![ -ι, 0 ]]

def σZ : Op 1 := ![
    ![ 1, 0 ],
    ![ 0, -1 ]]

-- Hadamard gate
noncomputable
def H : Op 1 := ![
    ![ 1/√2,  1/√2 ],
    ![ 1/√2, -1/√2 ]]

-- Controlled-NOT gate (aka CX gate)
def CNOT : Op 2 := ![
    ![ 1, 0, 0, 0 ],
    ![ 0, 1, 0, 0 ],
    ![ 0, 0, 0, 1 ],
    ![ 0, 0, 1, 0 ]]

-- Controlled-Z gate
def CZ : Op 2 := ![
    ![ 1, 0, 0, 0 ],
    ![ 0, 1, 0, 0 ],
    ![ 0, 0, 1, 0 ],
    ![ 0, 0, 0, -1 ]]

def SWAP : Op 2 :=
    ![ ![1, 0, 0, 0],
       ![0, 0, 1, 0],
       ![0, 1, 0, 0],
       ![0, 0, 0, 1]]


------------------------------------------------------------------------------
-- Controlled-U gates

/-- Controlled-U : |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U -/
def controlled {n : ℕ} (U : Op n) : Op (n + 1) := |0⟩⬝⟨0| ⊗ (I _) + |1⟩⬝⟨1| ⊗ U
/-- Controlled'-U : |1⟩⟨1| ⊗ I + |0⟩⟨0| ⊗ U -/
def controlled' {n : ℕ} (U : Op n) : Op (n + 1) := (σX ⊗ I _) ⬝ controlled U ⬝ (σX ⊗ I _)

------------------------------------------------------------------------------
-- Common projection operators

def P0 : Op 1 := ![
    ![ 1, 0 ],
    ![ 0, 0 ]]

def P1 : Op 1 := ![
    ![ 0, 0 ],
    ![ 0, 1 ]]

noncomputable
def P_plus : Op 1 := ![
    ![ 1/2, 1/2 ],
    ![ 1/2, 1/2 ]]

noncomputable
def P_minus : Op 1 := ![
    ![ 1/2, -(1/2) ],
    ![ -(1/2), 1/2 ]]
