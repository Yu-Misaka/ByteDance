import Mathlib

open Classical

/-- The property that a finite set of natural numbers `A` contains no subset of size `k`
where all pairs of distinct elements have the same least common multiple.

Formally, there does not exist a subset $S \subseteq A$ with $|S| = k$ and some integer $L$
such that $\text{lcm}(a, b) = L$ for all distinct $a, b \in S$.-/
def erdos_856_prop (k : ℕ) (A : Finset ℕ) :=
  ¬ ∃ S ⊆ A, S.card = k ∧
    ∃ L : ℕ, ∀ a b : S, a ≠ b → a.1.lcm b = L

/-- The set of all subsets of $\{1, \dots, N\}$ that satisfy the property `erdos_856_prop k`.-/
noncomputable def erdos_856_set (k N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (erdos_856_prop k)

/-- The set of all possible reciprocal sums $\sum_{n \in A} \frac{1}{n}$ where $A$ ranges over
all subsets of $\{1, \dots, N\}$ satisfying `erdos_856_prop k`.-/
noncomputable def erdos_856_set' (k N : ℕ) : Finset ℚ :=
  (erdos_856_set k N).image (·.sum fun n ↦ (1 / n : ℚ))

/-- Proof that `erdos_856_set` is nonempty for $k \ge 3$.
The empty set always satisfies the property since it has no subset of size $k$.-/
lemma erdos_856_set_nonempty {k N : ℕ} (hk : 3 ≤ k) : (erdos_856_set k N).Nonempty := by
  use ∅
  simp [erdos_856_set, erdos_856_prop]
  omega

/-- Proof that `erdos_856_set'` is nonempty for $k \ge 3$, derived from `erdos_856_set_nonempty`.-/
lemma erdos_856_set_nonempty' {k N : ℕ} (hk : 3 ≤ k) : (erdos_856_set' k N).Nonempty :=
  Finset.Nonempty.image (erdos_856_set_nonempty hk) _

/-- The function $f_k(N)$ representing the maximum value of $\sum_{n \in A} \frac{1}{n}$
where $A \subseteq \{1, \dots, N\}$ contains no subset of size $k$ with the same pairwise LCM.-/
noncomputable def erdos_856_f {k : ℕ} (hk : 3 ≤ k) (N : ℕ) : ℝ :=
  (erdos_856_set' k N).max' (erdos_856_set_nonempty' hk)

open Asymptotics Filter in
/-- Statement of Erdős Problem 856: Ask for an asymptotic estimate of $f_k(N)$.
This theorem asserts the existence of such an estimate (placeholder).-/
theorem erdos_856 (k : ℕ) (hk : 3 ≤ k) : ∃ (est : ℕ → ℝ),
  erdos_856_f hk =O[atTop] est := sorry
