import Mathlib

open Classical

/-- The property for a set $A$ that for any pair of elements $a, b \in A$ (not necessarily distinct),
the value $ab + 1$ contains a square factor.-/
def erdos_848_prop (A : Finset ℕ) : Prop := ∀ a b : A, ¬ Squarefree (a.1 * b.1 + 1)

/-- The proposed optimal set for Erdős Problem 848, consisting of all numbers up to `N`
that are congruent to 7 modulo 25.-/
def erdos_848_congr (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (· ≡ 7[MOD 25])

/-- The family of all subsets of $\{1, \ldots, N\}$ that satisfy the `erdos_848_prop` property.-/
noncomputable def erdos_848_sets (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter erdos_848_prop

/-- Proof that the modular set `erdos_848_congr` satisfies the required property.
Specifically, for $a, b \equiv 7 \pmod{25}$, we have $ab + 1 \equiv 50 \equiv 0 \pmod{25}$,
so $ab+1$ is divisible by $5^2$.-/
lemma erdos_848_congr_in_sets (N : ℕ) : erdos_848_congr N ∈ erdos_848_sets N := by
  simp [erdos_848_congr, erdos_848_sets, erdos_848_prop]
  intro a ha1 ha2 ha b hb1 hb2 hb
  simp [Nat.squarefree_iff_prime_squarefree]
  use 5, Nat.prime_five
  have := (Nat.ModEq.add_right 1 (Nat.ModEq.mul ha hb)).trans
    (Dvd.dvd.modEq_zero_nat (by decide))
  rwa [← Nat.modEq_zero_iff_dvd]

/-- The family of valid sets is nonempty (e.g., it contains the empty set or the modular set).-/
lemma erdos_848_sets_nonempty {N : ℕ} : (erdos_848_sets N).Nonempty := by
  use ∅
  simp [erdos_848_sets, erdos_848_prop]

/-- The set of cardinalities of all valid sets is nonempty.-/
lemma erdos_848_sets_nonempty' {N : ℕ} :
    ((erdos_848_sets N).image Finset.card).Nonempty :=
  Finset.Nonempty.image erdos_848_sets_nonempty _

/-- The maximum possible size of a subset of $\{1, \ldots, N\}$ satisfying `erdos_848_prop`.-/
noncomputable def erdos_848_max_size (N : ℕ) : ℕ :=
  ((erdos_848_sets N).image Finset.card).max' erdos_848_sets_nonempty'

open Asymptotics Filter in
/-- The statement of Erdős Problem 848.
It asserts that for sufficiently large $N$, the size of the set of numbers congruent to
7 modulo 25 is equal to the maximum possible size of a set satisfying the property.-/
theorem erdos_848 : ∀ᶠ N : ℕ in atTop,
    (erdos_848_congr N).card = erdos_848_max_size N := sorry
