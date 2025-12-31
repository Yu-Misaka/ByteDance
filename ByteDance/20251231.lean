import Mathlib

/-- The set of positive integers $n$ such that for every prime divisor $p$ of $n$,
there exists a divisor $d > 1$ of $n$ satisfying $d \equiv 1 \pmod{p}$.-/
def A : Set ℕ := {n | ∀ p ∈ n.primeFactors,
  ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d ≡ 1 [MOD p]}

open Asymptotics Filter in
/-- Erdős Problem 768:
There exists a constant $c > 0$ such that the density of $A$ in $[1, N]$ is given by
$\exp(-(c + o(1)) \sqrt{\log N} \log \log N)$ as $N \to \infty$.-/
theorem erdos_768 : ∃ c : ℝ, 0 < c ∧
  ∃ u : ℕ → ℝ, u =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ᶠ N : ℕ in atTop,
      (Nat.card (A ∩ Finset.Icc 1 N : Set ℕ) / N : ℝ) = Real.exp (
        - (c + u N) * Real.sqrt (Real.log N) * Real.log (Real.log N)) := sorry
