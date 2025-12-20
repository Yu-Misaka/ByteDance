import Mathlib

/-- The condition for Erdos Problem 635.
`con t S` states that for any two elements `a` and `b` in the set `S`,
if their difference is at least `t`, then their difference does not divide the larger element.-/
abbrev con (t : ℕ+) (A : Finset ℕ+) : Prop :=
  ∀ a b : A, t ≤ b.1 - a.1 → ¬ b.1 - a.1 ∣ b.1

open Classical

/-- The set of all possible cardinalities of subsets of $\{1, \ldots, N\}$
that satisfy the condition `con t`.-/
noncomputable abbrev A (t N : ℕ+) : Finset ℕ :=
  ((Finset.Icc 1 N).powerset.filter (con t)).image Finset.card

/-- Lemma stating that the set of possible sizes `A t N` is never empty.
This is true because the empty set is always a valid subset satisfying the condition.-/
lemma nonempty (t N : ℕ+) : (A t N).Nonempty := by
  use 0
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, Subtype.forall,
    Finset.card_eq_zero, exists_eq_right, Finset.empty_subset, Finset.notMem_empty,
    IsEmpty.forall_iff, implies_true, and_self]

/-- The function `f(N, t)` represents the maximum size of a subset of $\{1, \ldots, N\}$
satisfying the condition with parameter `t`.-/
noncomputable abbrev f (t N : ℕ+) : ℕ := (A t N).max' (nonempty t N)

open Asymptotics Filter in
/-- The formal statement of Erdos Problem 635.
It conjectures that there exists an error term `u(t)` which is $o(1)$ as $t \to \infty$,
such that the maximum size `f(N, t)` is bounded by $(1/2 + u(t))N$.-/
theorem erdos_635 : ∃ u : ℕ+ → ℝ,
    (u =o[atTop] fun _ ↦ (1 : ℝ)) ∧
    ∀ t N : ℕ+, f t N ≤ (1 / 2 + u t) * N := sorry
