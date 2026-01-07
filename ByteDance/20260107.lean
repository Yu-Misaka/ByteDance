import Mathlib

/-- The set of all perfect cubes in ℕ. -/
def A : Set ℕ := {n | ∃ x : ℕ, n = x ^ 3}

open Classical in
/-- The number of ways to represent `n` as a sum of two cubes.
This corresponds to the additive convolution of the indicator function of `A` with itself,
evaluated at `n`, i.e., $(1_A * 1_A)(n)$.

**Correctness Proof Sketch:**
1. `Finset.antidiagonal n` produces the finite set of all pairs `(a, b)` such that `a + b = n`.
2. The filter `ab ∈ (A ×ˢ A)` ensures that both `ab.1 ∈ A` and `ab.2 ∈ A` (both are cubes).
3. The cardinality (`.card`) counts how many such pairs exist.
Since $1_A(a) \cdot 1_A(b) = 1$ if $a, b \in A$ and $0$ otherwise, the sum
$\sum_{a+b=n} 1_A(a)1_A(b)$ is exactly the count of pairs $(a, b)$ in the antidiagonal
where both elements belong to $A$.-/
noncomputable def A_conv (n : ℕ) : ℕ :=
  (Finset.antidiagonal n).filter (fun ab ↦ ab ∈ (A ×ˢ A)) |>.card

open Asymptotics Filter in
/-- **Erdős Problem 829:**
Let $A\subset\mathbb{N}$ be the set of cubes. Is it true that\[1_A\ast 1_A(n) \ll (\log n)^{O(1)}?\]-/
theorem erdos_829 : ∃ u : ℕ → ℝ, u =O[atTop] (fun _ ↦ (1 : ℝ)) ∧
  (fun n ↦ (A_conv n : ℝ)) =O[atTop] (fun n ↦ (Real.log n) ^ (u n)) := sorry
