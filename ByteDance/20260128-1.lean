import Mathlib

/-- The magnitude (norm) of the sum of the `k`-th powers of the elements in the sequence `z`
indexed from `1` to `n`.

Given a sequence $z: \mathbb{N} \to \mathbb{C}$, this computes:
$$ \left| \sum_{i=1}^{n} z_i^k \right| $$. -/
noncomputable def erdos_973_sum (n : ℕ+) (z : ℕ+ → ℂ) (k : ℕ+) : ℝ :=
  ‖((Finset.Icc 1 n).sum (fun i ↦ (z i) ^ k.1))‖

/-- The maximum of `erdos_973_sum` with `n` ranging from `2` to `n + 1`.

i.e., \[\max_{2\leq k\leq n+1}\left\lvert \sum_{1\leq i\leq n}z_i^k\right\rvert\]. -/
noncomputable def erdos_973_sum_max (n : ℕ+) (z : ℕ+ → ℂ) : ℝ :=
  ((Finset.Icc 2 (n + 1)).image (erdos_973_sum n z)).max'
    <| Finset.Nonempty.image (Finset.nonempty_Icc.2
      (PNat.natPred_le_natPred.1 (by exact n.2))) _

/-- Does there exist a constant $C > 1$ such that for every integer $n \ge 2$,
there exists a sequence of complex numbers $z_1, \dots, z_n$ satisfying specific
norm and boundary conditions, such that their power sums are exponentially small? -/
theorem erdos_973 : ∃ (C : ℝ), 1 < C ∧
  ∀ n : ℕ+, 2 ≤ n → ∃ z : ℕ+ → ℂ,
    z 1 = 1 ∧
    (∀ i ≤ n, 1 ≤ ‖z i‖) ∧
    erdos_973_sum_max n z < C ^ (- n : ℤ) := sorry
