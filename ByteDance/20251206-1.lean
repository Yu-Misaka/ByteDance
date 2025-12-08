import Mathlib

open Filter Asymptotics

/-- A family of sets `F` is **union-free** if there are no solutions to the equation
`A ∪ B = C` where `A`, `B`, and `C` are distinct members of `F`.-/
def IsUnionFree (F : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, ([A, B, C].Pairwise (· ≠ ·)) → A ∪ B ≠ C

/-- Decidability instance for `IsUnionFree`.
This is required to use `IsUnionFree` as a predicate in `Finset.filter`.-/
instance : DecidablePred IsUnionFree := by
  delta IsUnionFree
  infer_instance

/-- The set of all union-free families of subsets of `{1, ..., n}`.
This constructs the finite search space for the extremal problem.-/
def 𝓕 (n : ℕ) := (Finset.Icc 1 n).powerset.powerset.filter IsUnionFree

/-- Proof that the set of cardinalities of union-free families is nonempty.
This is needed to safely define `f n` using `Finset.max'`.-/
lemma nonempty {n : ℕ} : (Finset.image Finset.card (𝓕 n)).Nonempty := by
  refine Finset.Nonempty.image ⟨∅, ?_⟩ Finset.card
  simp [𝓕, IsUnionFree]

/-- The extremal function for union-free families.
`f n` returns the maximum cardinality of a union-free collection of subsets of `{1, ..., n}`.-/
def f (n : ℕ) := ((𝓕 n).image Finset.card).max' nonempty

/-- The first part of Erdős Problem 447.
It asks whether the size of the largest union-free family is negligible compared to
the total number of subsets $2^n$ (i.e., is it $o(2^n)$?).-/
theorem erdos_447_1 :
  (fun n ↦ (f n : ℝ)) =o[atTop] (fun n : ℕ ↦ (2 ^ n : ℝ)) := sorry

/-- The second, stronger question of Erdős Problem 447.
It asks if the size of a union-free family is asymptotically bounded by the size of
the largest antichain, represented by the central binomial coefficient.
Specifically, is $|\mathcal{F}| < (1 + o(1)) \binom{n}{n/2}$?-/
theorem erdos_447_2 : ∃ u : ℕ → ℝ,
  u =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ᶠ n in atTop, (f n : ℝ) < (1 + u n) * (Nat.choose n (n / 2) : ℝ) := sorry
