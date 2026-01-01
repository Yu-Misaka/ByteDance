import Mathlib

/-- The conjecture that the set of perfect squares contains arbitrarily long quasi-progressions.

A sequence $x_1, x_2, \dots, x_k$ is a quasi-progression of error $C$ if there exists
a common difference $d$ such that $d \le x_{i+1} - x_i \le d + C$ for all $i$.
The problem asks if there exists a constant $C$ such that for every $k$,
the squares contain such a sequence of length $k$.-/
theorem erdos_782_1 : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ+,
  ∃ x : ℕ → ℕ,
    ∀ i : Finset.Icc 1 k, IsSquare (x i) ∧
    ∃ d : ℝ, ∀ i : Finset.Icc 1 k, i ≠ k →
      x i + d ≤ x (i + 1) ∧ x (i + 1) ≤ x i + d + C := sorry

/-- A Hilbert cube $H(a; b_1, \dots, b_k)$ is the set of all subset sums
$\{ a + \sum_{i \in S} b_i : S \subseteq \{0, \dots, k-1\} \}$.
"subset" here plays the same role as $\epsilon_i$ in the original problem.-/
def HilbertCube (a : ℕ) (k : ℕ+) (b : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).powerset.image (a + ·.sum (fun i ↦ b i))

/-- The conjecture that the set of perfect squares contains Hilbert cubes of
arbitrarily large cardinality.-/
theorem erdos_782_2 : ∀ N : ℕ,
  ∃ a : ℕ, ∃ k : ℕ+, ∃ b : ℕ → ℕ,
    N ≤ (HilbertCube a k b).card ∧
    ∀ x ∈ HilbertCube a k b, IsSquare x := sorry
