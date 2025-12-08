import Mathlib

variable {D : Type*} [CommRing D] [IsDomain D]
  (P : Ideal D) (hpri : P.IsPrime)

example (h : ¬ P.IsMaximal) : ∃ a : D, a ∉ P ∧ (Ideal.span {a} + P) ≠ ⊤ := by
  by_cases hP : P = ⊤
  · have := Ideal.IsPrime.ne_top hpri
    tauto
  by_contra!
  sorry

example (a : D) : (⟦Ideal.span {a} + P⟧ :(D ⧸ P))
