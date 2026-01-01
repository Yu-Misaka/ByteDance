import Mathlib

open Asymptotics Filter Classical Real

/-- A set of natural numbers `A` is a **Sidon set** (or $B_2$ set) if for any $a, b, c, d \in A$,
the equality $a + b = c + d$ implies the sets $\{a, b\}$ and $\{c, d\}$ are equal.-/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d : {n // n ∈ A}, a.1 + b.1 = c.1 + d.1 → ({a.1, b.1} : Set ℕ) = {c.1, d.1}

/-- The collection of all subsets of the first $N$ perfect squares $\{1^2, 2^2, \dots, N^2\}$
that satisfy the `IsSidon` property.-/
noncomputable def sidonSubsetsOfSquares (N : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 N).image (· ^ 2)).powerset.filter (fun S ↦ IsSidon S)

/-- The set of Sidon subsets of squares is never empty, as it always contains the empty set.-/
lemma sidonSubsetsOfSquares_nonempty (N : ℕ) : (sidonSubsetsOfSquares N).Nonempty := by
  use ∅
  simp [sidonSubsetsOfSquares, IsSidon]

/-- `maxSidonSize N` is the cardinality of the largest Sidon subset of $\{1^2, \dots, N^2\}$.-/
noncomputable def maxSidonSize (N : ℕ) : ℕ :=
  (sidonSubsetsOfSquares N).sup' (sidonSubsetsOfSquares_nonempty N) Finset.card

/--
**Erdős Problem 773**: Does the maximum size of a Sidon subset of the first $N$ squares
grow like $N^{1-o(1)}$?
This is expressed by saying there exists a sequence $u_N \to 0$ such that
the size equals $N^{1 - u_N}$ for sufficiently large $N$.
-/
theorem erdos_problem_773 :
    ∃ u : ℕ → ℝ, u =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ᶠ N : ℕ in atTop, (maxSidonSize N : ℝ) = (N : ℝ) ^ (1 - u N) :=
  sorry
