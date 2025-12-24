import Mathlib

/--
We say that $A \subset \mathbb{N}$ has the **translation property** if, for every $n$,
there exists some integer $t_n \geq 1$ such that, for all $1 \leq a \leq n$,
$a \in A \iff a + t_n \in A$.
-/
abbrev IsTranslation (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ tₙ : ℕ, 1 ≤ tₙ ∧
    (∀ a : ℕ, 1 ≤ a ∧ a ≤ n → (a ∈ A ↔ a + tₙ ∈ A))

/--
**Problem 1**: Does the set of the sums of two squares have the translation property?
-/
theorem erdos_675_1 :
  IsTranslation {x : ℕ | ∃ a b : ℕ, x = a ^ 2 + b ^ 2} := sorry

section part_2

open Asymptotics Filter

/--
A set of natural numbers $S$ (implicitly primes) has **large density** if its
cardinality up to $x$ is at least proportional to $\pi(x) \sim x / \log x$.
Formally, there exists $C$ such that for sufficiently large $x$,
$x / \log x \leq C \cdot |S \cap [0, x)|$.
-/
abbrev HasLargeDensity (S : Set ℕ) : Prop :=
  ∃ C : ℝ, ∀ᶠ x : ℕ in atTop,
    x / Real.log x ≤ C * Nat.card (S ∩ x.primesBelow : Set ℕ)

/-- The set of all prime numbers. -/
abbrev Primes : Set ℕ := {p : ℕ | p.Prime}

/--
A partition of primes into $P$ and $Q$ is considered **desired** if both parts
maintain a large density relative to the prime number theorem.
-/
abbrev IsDesiredPartition (P : Set ℕ) : Prop :=
  HasLargeDensity P ∧ HasLargeDensity (Primes \ P)

/--
**Problem 2**: If we partition all primes into $P \sqcup Q$ such that each set contains
$\gg x / \log x$ many primes, can the set of integers only divisible by primes from $P$
have the translation property?
-/
theorem erdos_675_2 : ∃ P : Set ℕ,
  P ⊆ Primes ∧ IsDesiredPartition P ∧
    IsTranslation {x : ℕ | ∀ p, p.Prime → p ∣ x → p ∈ P} := sorry

end part_2

/--
Auxiliary lemma: The set of squarefree numbers is known to have the translation property.
This justifies the existence of $t_n$ in the third problem.
-/
lemma squarefree_is_translation :
  IsTranslation {x : ℕ | Squarefree x} := sorry

open Classical in
/--
**Problem 3**: If $A$ is the set of squarefree numbers, how fast does the minimal such
$t_n$ grow? Is it true that $t_n > \exp(n^c)$ for some constant $c > 0$?
-/
theorem erdos_675_3 : ∃ c : ℝ, 0 < c ∧
  ∀ n : ℕ, Real.exp (n ^ c) < Nat.find (squarefree_is_translation n) := sorry
