import Mathlib

/-
## Implementation notes

**Indexing**: Standard mathematical literature usually denotes the first prime as $p_1 = 2$.
  In Lean/Mathlib, `Nat.nth Nat.Prime` is 0-indexed, so `p 0 = 2`. Consequently, the gap
  $d_n$ corresponds to the mathematical $d_{n+1}$ in 1-based indexing. This index shift
  does not affect the asymptotic behavior of $h(x)$ as $x \to \infty$.

**Intervals**: We use `Finset.Ico n (n + h)` to represent the range of indices $[n, n+h)$.
  This set has cardinality exactly $h$, avoiding off-by-one errors common with closed intervals
  when $h=0$.
-/

/-- The $n$-th prime number, defined using 0-based indexing.-/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The $n$-th prime gap, defined as $p_{n+1} - p_n$.-/
noncomputable def d (n : ℕ) : ℕ := p (n + 1) - p n

/-- Auxiliary lemma stating that for any $x$, there exists a length $h$ that is "too long".
Specifically, for a sufficiently large $h$, no sequence of gaps of length $h$ starting
below $x$ can consist of distinct elements.-/
lemma h_aux (x : ℕ) : ∃ h : ℕ, ∀ n < x,
    ¬ Set.InjOn d (Finset.Ico n (n + h)) := sorry

/-- The function $h(x)$ representing the maximal length of a distinct sequence of prime gaps
starting at an index $n < x$.
It is defined constructively as `find(h_aux) - 1`. Since `Nat.find` returns the **smallest**
length that fails to satisfy the distinctness property everywhere, subtracting 1 gives us
the **largest** length for which a valid sequence exists.-/
noncomputable def h (x : ℕ) := Nat.find (h_aux x) - 1

/-- Predicate stating that there exists a starting index $n < x$ such that the sequence of
prime gaps of length `len` starting at $n$ contains distinct values.-/
def erdos_852_prop (x h : ℕ) : Prop := ∃ n < x,
  Set.InjOn d (Finset.Ico n (n + h))

/-- Proof that `h(x)` is indeed the maximal length satisfying `erdos_852_prop`.-/
lemma h_prop {x : ℕ} (hx : 1 ≤ x) : Maximal (erdos_852_prop x) (h x) := by
  rw [maximal_iff_forall_gt]
  constructor
  · dsimp [erdos_852_prop, h]
    convert Nat.find_min (h_aux x) (m := Nat.find (h_aux x) - 1) ?_
    · grind only
    refine Nat.sub_one_lt fun h_con ↦ ?_
    simpa using (Nat.find_eq_zero (h_aux x)).1 h_con 0 (by omega)
  · intro y hy
    dsimp [erdos_852_prop]
    obtain ⟨n, ⟨h1, h2⟩⟩ := (Nat.find_le_iff (h_aux x) y).1 <| Nat.le_of_pred_lt hy
    simp at h2 ⊢
    intro z hz
    specialize h2 z hz
    contrapose! h2
    exact Set.InjOn.mono (Set.Ico_subset_Ico_right (by omega)) h2

open Asymptotics Filter

/-- Conjecture 1: The growth of $h(x)$ is bounded below by a power of $\log x$.
Note: `x` is restricted to `ℕ+` to ensure `log x` is well-behaved and positive.-/
theorem erdos_852_1 : ∃ c > (0 : ℝ), ∀ x : ℕ+, (Real.log x) ^ c < (h x : ℝ) :=
  sorry

/-- Conjecture 2: The growth of $h(x)$ is strictly slower than $\log x$ (little-o notation).-/
theorem erdos_852_2 : (fun x ↦ (h x : ℝ)) =o[atTop] (fun x : ℕ ↦ Real.log x) :=
  sorry
