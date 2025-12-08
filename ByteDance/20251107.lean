import Mathlib

/-
For integers $1\leq a < b$ let $D(a,b)$ be the minimal value of $n_k$ such that there exist integers
$1\leq n_1<\cdots < n_k$ with
\[\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.\]
Estimate $D(b)=\max_{1\leq a < b}D(a,b)$. Is it true that
\[D(b) \ll b(\log b)^{1+o(1)}?\]
-/

section test

namespace testflight

-- variable (a : ℕ+) (b : ℕ) (hab : a < b)

abbrev D_prop (a : ℕ+) (b : ℕ) : ∃ nₖ : ℕ, (∃ k : ℕ+, (∃ n : Finset.Icc 1 k → ℕ,
  StrictMono n ∧
  1 ≤ n ⟨1, Finset.left_mem_Icc.mpr k.2⟩ ∧
  n ⟨k, Finset.right_mem_Icc.mpr k.2⟩ = nₖ ∧
  (a / b : ℚ) = ∑ i, (1 / (n i) : ℚ))) := sorry

#check Nat.find
#check D_prop

open Classical in
noncomputable def D (a : ℕ+) (b : ℕ) := Nat.find <| D_prop a b

-- def D' (b : ℕ) :=

end testflight

namespace testflight2

class EgyptianRepr {a b : ℕ} (hab : 1 ≤ a ∧ a < b) where
  ns : List ℕ
  validity : ns ≠ []
  strict_mono : ns.Pairwise (· < ·)
  head : 1 ≤ ns.head validity
  sum : (ns.map (fun x ↦ (1 / x : ℚ))).sum = a / b

def IsLastOfEgyptian {a b : ℕ} (hab : 1 ≤ a ∧ a < b) (n : ℕ): Prop :=
  ∃ repr : EgyptianRepr hab, repr.ns.getLast repr.validity = n

open Classical in
noncomputable def D (a b : ℕ) : ℕ :=
  if hab : 1 ≤ a ∧ a < b then
    if h : ∃ nₖ, IsLastOfEgyptian hab nₖ then
      Nat.find h
    else 0
  else 0

noncomputable def Db (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup (fun a ↦ D a b)

open Filter Topology in
theorem D_b_upper_bound_form1 :
  ∃ (C : ℝ) (u : ℕ → ℝ),
    Tendsto u atTop (𝓝 0) ∧
    ∀ᶠ b in atTop, Db b ≤ C * (b : ℝ) * (Real.log (b : ℝ))^(1 + u b) := sorry

end testflight2

end test

/-
For integers $1\leq a < b$ let $D(a,b)$ be the minimal value of $n_k$ such that there exist integers
$1\leq n_1<\cdots < n_k$ with \[\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.\]
Estimate $D(b)=\max_{1\leq a < b}D(a,b)$. Is it true that \[D(b) \ll b(\log b)^{1+o(1)}?\]
-/

/--
An `EgyptianRepr hab` packages the data of an *Egyptian fraction representation*
of a rational number `a / b` with 1 ≤ a < b.
Mathematically, it corresponds to a finite strictly increasing sequence
of positive integers n₁ < ⋯ < nₖ such that a / b = ∑ (1 / nᵢ).
-/
class EgyptianRepr {a b : ℕ} (hab : 1 ≤ a ∧ a < b) where
  /-- `ns` : the underlying list [n₁, …, nₖ];-/
  ns : List ℕ
  /-- `validity` : the list is nonempty (so nₖ is well-defined);-/
  validity : ns ≠ []
  /-- `strict_mono` : the entries are strictly increasing;-/
  strict_mono : ns.Pairwise (· < ·)
  /-- `head` : ensures n₁ ≥ 1 (hence all nᵢ ≥ 1);-/
  head : 1 ≤ ns.head validity
  /-- `sum` : the defining identity of the Egyptian fraction.-/
  sum : (ns.map (fun x ↦ (1 / x : ℚ))).sum = a / b

/--
`IsLastOfEgyptian hab n` means that there exists a valid Egyptian
representation of `a / b` whose **largest denominator** (i.e. last element
of the increasing list) equals `n`.
This auxiliary predicate is used to define D(a, b)
as the smallest such possible `n`.
-/
def IsLastOfEgyptian {a b : ℕ} (hab : 1 ≤ a ∧ a < b) (n : ℕ) : Prop :=
  ∃ repr : EgyptianRepr hab, repr.ns.getLast repr.validity = n

open Classical in
/--
`D a b` is the minimal possible value of the last denominator `nₖ`
appearing in an Egyptian fraction representation of `a / b`.
If `a` and `b` do not satisfy 1 ≤ a < b, or if there is no such
representation, we define `D a b = 0`.
This use of `0` as a "junk value" is safe, since we later prove that
no genuine representation can have `nₖ = 0`. Hence `0` acts as a
syntactically valid but semantically distinct default.
-/
noncomputable def D (a b : ℕ) : ℕ :=
  if hab : 1 ≤ a ∧ a < b then
    if h : ∃ nₖ, IsLastOfEgyptian hab nₖ then
      -- returns the minimal such nₖ
      Nat.find h
    -- no representation exists
    else 0
  -- invalid (a,b) pair
  else 0

/--
In any nonempty strictly increasing list of natural numbers,
the head is less than or equal to the last element.
This simple lemma is used to ensure positivity of denominators.
-/
lemma strict_mono_list (ns : List ℕ) (hmono : ns.Pairwise (· < ·)) (hvalid : ns ≠ []) :
    ns.head hvalid ≤ ns.getLast hvalid := by
  induction ns with
  | nil => tauto
  | cons x xs ih =>
    rw [List.pairwise_cons] at hmono
    by_cases hxs : xs = []
    · subst xs
      simp only [List.head_cons, List.getLast_singleton, le_refl]
    specialize ih hmono.2 hxs
    simp [List.getLast_cons hxs]
    refine le_trans ?_ ih
    exact Nat.le_of_succ_le <| hmono.1 (xs.head hxs) (List.head_mem hxs)

/--
No valid Egyptian representation can have last denominator equal to 0.
This ensures that the value `0` in the definition of `D a b` can safely
be used as a sentinel (i.e., an indicator of "no valid representation").
-/
lemma egy_repr_ne_zero {a b : ℕ} (hab : 1 ≤ a ∧ a < b) : ¬ IsLastOfEgyptian hab 0 := by
  simp [IsLastOfEgyptian]
  exact fun x ↦ Nat.ne_zero_of_lt <|
    x.head.trans <| strict_mono_list x.ns x.strict_mono x.validity

/--
A conceptual lemma explaining the meaning of the default value `0`:
`D a b = 0` if and only if there exists **no** valid pair (a, b) with
an Egyptian representation of `a / b`.
Thus, `0` is not an arbitrary junk value but a canonical way to indicate
"no solution exists".
-/
lemma D_eq_zero_iff_trivial (a b : ℕ) :
    D a b = 0 ↔ ¬ (∃ hab : 1 ≤ a ∧ a < b, ∃ nₖ, IsLastOfEgyptian hab nₖ) := by
  constructor
  · intro hD
    by_contra!
    rcases this with ⟨hab, h⟩
    simp [D, hab, h] at hD
    exact (egy_repr_ne_zero hab) hD
  simp [D]
  tauto

/--
For each fixed denominator `b`, define
    D(b) = max_{1 ≤ a < b} D(a, b).
The maximum is implemented as a finite supremum over the range {1, …, b−1}.
-/
noncomputable def Db (b : ℕ) : ℕ :=
  (Finset.Ico 1 b).sup (fun a ↦ D a b)

open Filter Asymptotics in
/--
Erdős problem 305 (informal statement):
There exists a function u(b) → 0 such that
    D(b) = O( b (log b)^{1 + u(b)} )
as b → ∞. In Landau notation, this is written
    D(b) ≪ b (log b)^{1 + o(1)}.
-/
theorem erdos_305 :
  ∃ (u : ℕ → ℝ),
    u =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    (fun b ↦ (Db b : ℝ)) =O[atTop] (fun b ↦ b * (Real.log b) ^ (1 + u b)) := sorry

open Filter Topology in
theorem erdos_305' :
  ∃ (C : ℝ) (u : ℕ → ℝ),
    Tendsto u atTop (𝓝 0) ∧
    ∀ᶠ b in atTop, Db b ≤ C * b * (Real.log b) ^ (1 + u b) := sorry
