import data.complex.basic
import data.matrix.basic 
import tactic.omega.main

def x : complex := {re := 0.0, im := 0.0}

theorem x2_eq_x : x * x = x :=
begin
  unfold x,
  apply complex.ext; simp,
end

def m : matrix (fin 3) (fin 3) complex := λ i j, begin
  exact 0
end

theorem m2_eq_m : m * m = m := begin
  unfold m,
  simp,
  unfold matrix.mul,
  unfold matrix.dot_product,
  simp,
end

def I : matrix (fin 2) (fin 2) complex := λ i j, if i = j then 1.0 else 0.0
def X : matrix (fin 2) (fin 2) complex := λ i j, if i = j then 0.0 else 1.0
def Z : matrix (fin 2) (fin 2) complex := λ i j, if i = j then (if i.val = 0 then 1.0 else -1.0) else 0.0

theorem Z2_I : Z * Z = I := begin 
  unfold Z I,
  simp,
  unfold matrix.mul,
  unfold matrix.dot_product,
  simp,
  funext,
  cases i; cases k; simp,
  cases i_val; simp,
  cases k_val; simp,
  cases i_val; cases k_val; simp; exfalso,
  repeat{sorry},
  -- why the hell does omega not work here.
  -- I have H : k_val.succ.succ < 2
  -- ITS FALSE! WHY CANT IT FIGURE THAT OUT!
end

theorem stupid : ∀ (k : ℕ), k.succ.succ < 2 -> false := begin
  intros k H,
  

end