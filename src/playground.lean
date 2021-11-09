import data.complex.basic

def x : complex := {re := 0.0, im := 0.0}

theorem x2_eq_x : x * x = x :=
begin
  unfold x,
  apply complex.ext; simp,
end
