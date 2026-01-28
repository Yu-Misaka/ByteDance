import Mathlib

open Polynomial Complex

section definition

variable (f : ℂ[X]) (hf : f ≠ 0)

local notation3 "d" => f.natDegree

include hf in
variable {f} in
/-- Helper lemma stating that the length of the coefficient list is equal to the degree plus one. -/
lemma a_aux : d + 1 = f.coeffList.length := by
  simp [length_coeffList_eq_ite, hf]

variable {f} in
/-- The sequence of coefficients of `f`, indexed by `Fin (d + 1)`.
`a 0` corresponds to the constant term, and `a d` to the leading coefficient. -/
def a : Fin (d + 1) → ℂ :=
  f.coeffList.get.comp (Fin.cast (a_aux hf))

variable {f} in
/-- Helper lemma stating that the number of roots (counting multiplicity) equals the degree. -/
lemma z_aux : d = f.roots.toList.length := by
  rw [Multiset.length_toList, @natDegree_eq_card_roots ℂ ℂ _ _ f
    (RingHom.id ℂ) (IsAlgClosed.splits f), map_id]

/-- The sequence of roots of `f` in the complex plane, indexed by `Fin d`. -/
noncomputable def z : Fin d → ℂ :=
  f.roots.toList.get.comp (Fin.cast z_aux)

variable {f} in
/-- Helper lemma for the length of the list of arguments. -/
lemma θ_aux : d = (f.roots.toList.map (Real.pi + arg ·)).length := by
  rw [List.length_map, z_aux]

/-- The arguments (angles) of the roots of `f`.
Note: Standard `arg` in Mathlib returns values in `(-π, π]`. Here we shift the values
by `π` to map them into `[0, 2π]` for convenience in the problem statement. -/
noncomputable def θ : Fin d → ℝ :=
  (f.roots.toList.map (Real.pi + arg ·)).get.comp (Fin.cast θ_aux)

variable {f} in
/-- Proof that the normalized arguments `θ` lie within the interval `[0, 2π]`. -/
lemma θ_range (i : Fin d) : θ f i ∈ Set.Icc 0 (2 * Real.pi) := by
  simp [θ]
  refine ⟨?_, ?_⟩
  · nth_rw 1 [← neg_neg (Real.pi), add_comm, ← sub_eq_add_neg]
    refine sub_nonneg_of_le (le_of_lt ?_)
    exact neg_pi_lt_arg _
  · rw [two_mul, add_le_add_iff_left]
    exact arg_le_pi _

/-- The count of roots of `f` whose arguments lie within the given interval `I`. -/
noncomputable def actual_count (I : Set ℝ) : ℕ := {i : Fin d | θ f i ∈ I}.ncard

/-- The number of non-zero coefficients of `f` (sparsity). -/
noncomputable def n : ℕ := (f.coeffList.filter (· ≠ 0)).length

/-- The quantity `M` defined in Erdős Problem 990.
It is given by $M = \frac{\sum |a_i|}{\sqrt{|a_0| |a_d|}}$.
Note: This value is undefined (division by zero) if the constant term $a_0$ is zero. -/
noncomputable def M : ℝ :=
  (∑ i : Fin (d + 1), ‖(a hf i)‖) /
  Real.sqrt (‖a hf 0‖ * ‖a hf ⟨d, lt_add_one d⟩‖)

end definition

/--
**Erdős Problem 990**:

There exists an absolute constant `C` such that for any polynomial `f`
(with non-zero constant term, to avoid division by zero in `M`),
the discrepancy of the distribution of the arguments of its roots is bounded by
`C * sqrt(n * log M)`.

The inequality states:
$$ \left| \#\{\theta_i \in [\alpha, \beta]\} - \frac{\beta - \alpha}{2\pi} d \right| \le C \sqrt{n \log M} $$

where:
* `d` is the degree of the polynomial.
* `n` is the number of non-zero coefficients.
* `M` is the normalized coefficient sum defined above.
-/
theorem erdos_990 : ∃ C : ℝ, ∀ f : ℂ[X], (hf : f ≠ 0 ∧ f.coeff 0 ≠ 0) →
  ∀ (α β : ℝ), 0 ≤ α ∧ α ≤ β ∧ β ≤ 2 * Real.pi →
    |(actual_count f (Set.Icc α β) : ℝ) - (((β - α) * f.natDegree) / (2 * Real.pi))| ≤
      C * Real.sqrt (n f * Real.log (M f hf.1)) := sorry
