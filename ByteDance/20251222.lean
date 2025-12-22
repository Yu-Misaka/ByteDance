import Mathlib

/-
Let $k\geq 2$ and $q(n,k)$ denote the least prime which does not divide $\prod_{1\leq i\leq k}(n+i)$. Is it true that, if $k$ is fixed and $n$ is sufficiently large, we have\[q(n,k)<(1+o(1))\log n?\]
-/

variable {k : ℕ} (hk : 2 ≤ k)

variable (k) in
abbrev prod (n : ℕ) := ∏ i ∈ Finset.Icc 1 k, (n + i)

abbrev Nat.primesLeq (n : ℕ) := (Finset.Icc 1 n).filter Nat.Prime

abbrev leastPrime (n : ℕ) := n.primesLeq \ n.primeFactors

lemma leastPrime_nonempty {n : ℕ} (hn : 2 < n) : (leastPrime n).Nonempty := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 (show 1 < n - 1 by omega)
  use p
  rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, fun h ↦ ?_⟩
  · exact Nat.Prime.one_le <| Nat.prime_of_mem_primeFactors hp
  · have : p ≤ n - 1 := Nat.le_of_mem_primeFactors hp
    omega
  · exact Nat.prime_of_mem_primeFactors hp
  replace hp := Nat.dvd_sub h.2.1 <| Nat.dvd_of_mem_primeFactors hp
  rw [Nat.sub_sub_self <| Nat.one_le_of_lt hn, Nat.dvd_one] at hp
  subst hp; tauto

lemma prod_two {n : ℕ} (hn : 1 ≤ n) : 2 < prod 2 n := by
  simp [prod, show Finset.Icc 1 2 = {1, 2} by decide]
  grind only

lemma prod_incr (k1 k2 n : ℕ) (h : k1 ≤ k2) : prod k1 n ≤ prod k2 n := by
  simp [prod]
  refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
  · refine Finset.Icc_subset_Icc_right h
  rintro i hi -
  simp at hi
  suffices 1 ≤ i from Nat.le_add_left_of_le this
  exact hi.1

include hk in
lemma prod_gt_two {n : ℕ} (hn : 1 ≤ n) : 2 < prod k n :=
  match k with
  | 2 => prod_two hn
  | m + 2 => Nat.lt_of_lt_of_le (prod_two hn) (prod_incr 2 (m + 2) n hk)

include hk in
abbrev q (n : ℕ) :=
  if hn : 1 ≤ n then
    (leastPrime (prod k n)).min' <| leastPrime_nonempty (prod_gt_two hk hn)
  else 0

open Asymptotics Filter
theorem erdos_663 : ∃ u : ℕ → ℝ, u =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ᶠ n in atTop, q hk n < (1 + u n) * Real.log n := sorry
