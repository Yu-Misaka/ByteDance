import Mathlib

/-
  Let $A,B\subseteq \mathbb{N}$ such that for all large $N$\[\lvert A\cap \{1,\ldots,N\}\rvert \gg N^{1/2}\]and\[\lvert B\cap \{1,\ldots,N\}\rvert \gg N^{1/2}.\]It is not true that there are infinitely many solutions to $a_1-a_2=b_1-b_2\neq 0$ with $a_1,a_2\in A$ and $b_1,b_2\in B$
-/

section testflight

def sect (A : Set ℕ) (N : ℕ) : Set ℕ := A ∩ (Finset.Icc 1 N)

instance {A : Set ℕ} {N : ℕ} : Finite (sect A N) :=
  Finite.Set.finite_inter_of_right A ↑(Finset.Icc 1 N)

open Asymptotics Filter
class A_class where
  carrier : Set ℕ
  prop : (· ^ (1 / 2) : ℕ → ℝ) =O[atTop] (fun N ↦ (Nat.card (sect carrier N) : ℝ))

structure solution (A B : A_class) where
  a₁ : ℕ
  a₂ : ℕ
  b₁ : ℕ
  b₂ : ℕ
  mem_1 : a₁ ∈ A.carrier ∧ a₂ ∈ A.carrier
  mem_2 : b₁ ∈ B.carrier ∧ b₂ ∈ B.carrier
  eq  : (a₁ - a₂ : ℤ) = b₁ - b₂
  neq : (a₁ - a₂ : ℤ) ≠ 0

example : ¬ (∀ A B : A_class, Infinite (solution A B)) := sorry

end testflight

open Asymptotics Filter

/--
`initialSegment A N` :
The subset of `A` consisting of all elements ≤ N, i.e. A ∩ [1, N].
This corresponds to the set {1,…,N} ∩ A appearing in the original problem.
-/
def initialSegment (A : Set ℕ) (N : ℕ) : Set ℕ :=
  A ∩ (Finset.Icc 1 N).toSet

/--
`initialSegment A N` is always finite.
We declare a `Finite` instance so that its cardinality `Nat.card` is well-defined.
-/
instance {A : Set ℕ} {N : ℕ} : Finite (initialSegment A N) :=
  Finite.Set.finite_inter_of_right _ (Finset.Icc 1 N).toSet

/--
`RootDenseSet` :
A class representing subsets of ℕ that are **root-dense**,
meaning they grow at least on the order of N^(1/2).
Formally:
  (N ↦ N^(1/2)) =O[atTop] (N ↦ |A ∩ [1, N]|)
which means |A ∩ [1, N]| ≥ c * N^(1/2) for large N.
This matches the asymptotic lower bound from the problem statement.
-/
class RootDenseSet where
  carrier : Set ℕ
  growth  : (· ^ (1 / 2) : ℕ → ℝ) =O[atTop]
    (fun N ↦ (Nat.card (initialSegment carrier N) : ℝ))

/--
`DiffSolution` :
A structure representing a **solution quadruple**
(a₁, a₂, b₁, b₂) satisfying
  a₁, a₂ ∈ A,
  b₁, b₂ ∈ B,
  a₁ - a₂ = b₁ - b₂ ≠ 0.
This encodes exactly the type of equal nonzero differences
the Erdős problem asks about.
-/
structure DiffSolution (A B : RootDenseSet) where
  a₁ : ℕ
  a₂ : ℕ
  b₁ : ℕ
  b₂ : ℕ
  memA : a₁ ∈ A.carrier ∧ a₂ ∈ A.carrier
  memB : b₁ ∈ B.carrier ∧ b₂ ∈ B.carrier
  eq_diff : (a₁ - a₂ : ℤ) = b₁ - b₂
  nonzero : (a₁ - a₂ : ℤ) ≠ 0

/--
`erdos_problem_331` : Main theorem statement.
It asserts that not all root-dense sets A, B produce infinitely many
such `DiffSolution`s.
-/
theorem erdos_problem_331 :
    ¬ ∀ A B : RootDenseSet, Infinite (DiffSolution A B) := sorry
