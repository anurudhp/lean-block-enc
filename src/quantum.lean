import data.matrix.basic
import data.complex.basic
open matrix
open_locale complex_conjugate

-- `n`-qubit operator
abbreviation QubitState (n : ℕ) := fin (2^n) → ℂ
abbreviation QubitOp (n : ℕ) := matrix (fin (2^n)) (fin (2^n)) ℂ

-- `n`-qubit Identity operator
def I {n : ℕ} : QubitOp n := λ i j, if i = j then 1 else 0

-- dagger of an `n`-qubit operator
def dagger {n : ℕ} (A : QubitOp n) : QubitOp n := λ i j, conj (A j i)

def Hermitian {n : ℕ} (H : QubitOp n) : Prop := H = dagger H 
def Unitary {n : ℕ} (U : QubitOp n) : Prop := dagger U * U = @I n

def applyOp {n : ℕ} (A : QubitOp n) (ψ : QubitState n) : QubitState n := mul_vec A ψ