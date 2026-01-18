import Mathlib

/-- The $k$-th primorial, denoted $n_k$, defined as the product of the first $k$ prime numbers.-/
noncomputable def n (k : ℕ) : ℕ :=
  (Finset.range k).prod (Nat.nth Nat.Prime)

/-- The ordered list of positive integers strictly less than $n_k$ that are coprime to $n_k$.
Represents the reduced residue system modulo $n_k$.-/
noncomputable def as (k : ℕ) : List ℕ :=
  (List.Ico 1 (n k)).filter (n k).Coprime

/-- The sequence of differences (gaps) between consecutive elements of the reduced residue system.
Formally, if `as k` is the sequence $a_1, a_2, \dots$, this list contains $a_{i+1} - a_i$.-/
noncomputable def das (k : ℕ) : List ℕ :=
  List.zipWith (· - ·) (as k).tail (as k)

/-- Auxiliary lemma stating that there exists a positive even integer that does not appear
in the sequence of gaps `das k`.-/
def smallest_even_aux (k : ℕ) : ∃ n > 0, Even n ∧ n ∉ das k := by
  by_cases hd : das k = []
  · use 2, by decide, by decide, hd ▸ List.not_mem_nil
  let m := (das k).max?
  obtain ⟨a, ha⟩ : ∃ a : ℕ, m = some a :=
    Option.ne_none_iff_exists'.mp fun h ↦
      hd <| List.max?_eq_none_iff.1 h
  refine ⟨2 * a + 2, by positivity, ?_, fun h ↦ ?_⟩
  · apply Even.add <;> simp
  linarith [(List.max?_eq_some_iff.1 ha).right _ h]

/-- The smallest positive even integer that is **not** of the form $a_{i+1} - a_i$.
Erdős asks to estimate the growth of this value as $k \to \infty$.-/
noncomputable def smallest_even (k : ℕ) : ℕ := Nat.find (smallest_even_aux k)

/-- Lemma asserting that for $k \ge 2$, the list of gaps is not empty.
Necessary for defining the maximum gap.-/
lemma das_nonempty {k : ℕ} (h : 2 ≤ k) : (das k).toFinset.Nonempty := sorry

/-- The maximum difference between consecutive integers coprime to $n_k$.
This corresponds to the value of Jacobsthal's function $g(n_k)$.
Returns 0 if $k < 2$.-/
noncomputable def J (k : ℕ) : ℕ := if h : 2 ≤ k then
  (das k).toFinset.max' (das_nonempty h) else 0

/-- The number of distinct values appearing in the sequence of gaps `das k`.
Erdős asks whether $D(n_k) \gg J(n_k)$.-/
noncomputable def D (k : ℕ) : ℕ := (das k).dedup.length

open Asymptotics Filter

/-- Statement of the first part of Erdős Problem 854:
Estimate the growth rate of `smallest_even k`.
(Currently formalized as an existence statement for an asymptotic upper bound).-/
theorem erdos_854_1 : ∃ (est : ℕ → ℝ),
  (fun k ↦ (smallest_even k : ℝ)) =O[atTop] est := sorry

/-- Statement of the second part of Erdős Problem 854:
Conjecture that the number of distinct gaps is asymptotically bounded below
by the size of the maximum gap (up to a constant factor).
Formally: $J(n_k) = O(D(n_k))$.-/
theorem erdos_854_2 :
  (fun k ↦ (J k : ℝ)) =O[atTop] (fun k ↦ (D k : ℝ)) := sorry
