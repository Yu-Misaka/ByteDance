import Mathlib

open Set Pointwise Filter Asymptotics

/-- A set `A` is an additive basis of order `h` if the `h`-fold sumset `h • A`
covers the entire set of natural numbers.
In `Mathlib`, `h • A` denotes the set `{a₁ + ... + aₕ | aᵢ ∈ A}`.-/
def IsAdditiveBasis (A : Set ℕ) (h : ℕ) : Prop :=
  (h • A) = univ

/-- The initial segment of a set `A` up to `N`, defined as the intersection
of `A` with the interval `[1, N]`.
This represents the set used to calculate the counting function $A(N)$.-/
def initialSegment (A : Set ℕ) (N : ℕ) : Set ℕ :=
  A ∩ (Finset.Icc 1 N).toSet

/-- Instance guaranteeing that the `initialSegment` is always finite,
which allows the use of `Nat.card`.-/
instance {A : Set ℕ} {N : ℕ} : Finite (initialSegment A N) :=
  Finite.Set.finite_inter_of_right _ (Finset.Icc 1 N).toSet

/--
The formal statement corresponding to a negative answer to Erdős Problem 337.

It asserts that given a set `A` which is an additive basis of finite order
and has asymptotic density zero (Little-o of $N$), the ratio of the cardinality
of the sumset `A + A` to the cardinality of `A` (restricted to `[1, N]`)
does **not** tend to infinity as `N` goes to infinity.-/
theorem erdos_problem_337 :
  ∃ A : Set ℕ,
    (∃ n : ℕ, IsAdditiveBasis A n) ∧
    ((fun N ↦ (Nat.card (initialSegment A N) : ℝ)) =o[atTop] (Nat.cast : ℕ → ℝ)) →
  ¬ Tendsto (fun N ↦
    (Nat.card (initialSegment (A + A) N) : ℝ) / (Nat.card (initialSegment A N) : ℝ)) atTop atTop :=
  sorry
