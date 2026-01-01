import Mathlib

open Asymptotics Filter Topology

/-- The existence of a finite `m` such that `gcd_{a=2..m} (aⁿ - 1) = 1`.
This is a prerequisite for defining the function `h(n)`.-/
lemma exists_h (n : ℕ) :
  ∃ m : ℕ, ((Finset.Icc 2 m).image (· ^ n - 1)).gcd id = 1 := sorry

/-- `h n` is the smallest integer `m` such that `gcd(2ⁿ-1, 3ⁿ-1, ..., mⁿ-1) = 1`.
Mapped to `Nat.find` using the existence lemma.-/
def h (n : ℕ) := Nat.find (exists_h n)

/-- The set of integers `m` in the range `[1, n]` such that `h(m)` equals a given prime `p`.
This represents the counting function for the natural density.-/
def δ (p : Nat.Primes) (n : ℕ) := {m : ℕ | h m = p} ∩ Finset.Icc 1 n

/-- **Erdős Problem 770 (Part 1)**:
For every prime `p`, the natural density of the set `{n | h(n) = p}` exists.-/
theorem erdos_770_1 {p : Nat.Primes} : ∃ d : ℝ,
  Tendsto (fun n : ℕ ↦ (Nat.card (δ p n) / n : ℝ)) atTop (𝓝 d) := sorry

/-- **Erdős Problem 770 (Part 2)**:
The limit inferior of `h(n)` as `n` approaches infinity is infinite.-/
theorem erdos_770_2 : ∀ k : ℕ, k < liminf (fun n : ℕ ↦ (h n : ℝ)) atTop := sorry

/-- **Erdős Problem 770 (Part 3)**:
If `p` is the greatest prime such that `p - 1` divides `n`, and `p` is
sufficiently large relative to `n` (governed by `ε`), then `h(n) = p`.-/
theorem erdos_770_3 {n : ℕ} {ε : ℝ} (hε : 0 < ε) : ∀ p : ℕ,
  (Maximal (fun p : ℕ ↦ p.Prime ∧ p - 1 ∣ n) p) ∧ (n : NNReal) ^ ε < p →
    h n = p := sorry
