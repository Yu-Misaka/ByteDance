import Mathlib

/--
The product of `k` consecutive integers starting from `n + 1`.
That is, `∏_{i=1}^k (n + i)`.
-/
abbrev prod (k n : ℕ) := ∏ i ∈ Finset.Icc 1 k, (n + i)

/--
The product of 2 consecutive integers starting from `n + 1` is strictly greater than 2
for any `n ≥ 1`.
-/
lemma prod_two {n : ℕ} (hn : 1 ≤ n) : 2 < prod 2 n := by
  simp [prod, show Finset.Icc 1 2 = {1, 2} by decide]
  grind only

/--
The product of consecutive integers is monotonic in the number of terms `k`.
-/
lemma prod_incr (k1 k2 n : ℕ) (h : k1 ≤ k2) : prod k1 n ≤ prod k2 n := by
  simp [prod]
  refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
  · refine Finset.Icc_subset_Icc_right h
  rintro i hi -
  simp at hi
  suffices 1 ≤ i from Nat.le_add_left_of_le this
  exact hi.1

/--
For `k ≥ 2` and `n ≥ 1`, the product of `k` consecutive integers starting from `n + 1`
is strictly greater than 2.
-/
lemma prod_gt_two {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) : 2 < prod k n :=
  match k with
  | 2 => prod_two hn
  | m + 2 => Nat.lt_of_lt_of_le (prod_two hn) (prod_incr 2 (m + 2) n hk)

/--
For any `k ≥ 2` and `n ≥ 1`, there exists a prime `p` that does not divide `prod k n`.
The proof constructs such a prime as a factor of `prod k n - 1`.
-/
lemma exists_prime {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ prod k n := by
  have hprod := prod_gt_two hk hn
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 (show 1 < prod k n - 1 by omega)
  use p
  refine ⟨?_, fun h ↦ ?_⟩
  · exact Nat.prime_of_mem_primeFactors hp
  have hp' := Nat.dvd_sub h <| Nat.dvd_of_mem_primeFactors hp
  rw [Nat.sub_sub_self <| Nat.one_le_of_lt hprod, Nat.dvd_one] at hp'
  simp [hp'] at hp; tauto

/--
`q n hk` is the least prime which does not divide the product of `k` consecutive integers
starting from `n + 1`.
defined as 0 if `n = 0`.
-/
abbrev q {k : ℕ} (n : ℕ) (hk : 2 ≤ k) :=
  if hn : 1 ≤ n then Nat.find (exists_prime hk hn) else 0

open Asymptotics Filter in
/--
The statement of **Erdős problem 663**.

It asks whether, for fixed `k ≥ 2`, the least prime `q(n, k)` not dividing the product
of `k` consecutive integers satisfies `q(n, k) < (1 + o(1)) log n` as `n → ∞`.
-/
theorem erdos_663 {k : ℕ} (hk : 2 ≤ k) :
    ∃ u : ℕ → ℝ, u =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ᶠ n in atTop, q n hk < (1 + u n) * Real.log n := sorry
