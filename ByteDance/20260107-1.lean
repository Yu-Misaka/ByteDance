import Mathlib

/-- `IsNNeg a` states that the strictly increasing sequence `a` starts with a value
greater than or equal to 1. Since `a` is an order embedding into `ℕ`, this implies
all terms are positive integers.-/
def IsNNeg (a : ℕ+ ↪o ℕ) : Prop :=
  1 ≤ a 1

/-- `IsNotSum a` states the core condition of Erdős problem 839: no term $a_i$ is
the sum of a consecutive sub-segment of earlier terms.
Formally, for any $i$, there do not exist indices $j \le k < i$ such that
$a_i = \sum_{m=j}^k a_m$.-/
def IsNotSum (a : ℕ+ ↪o ℕ) : Prop :=
  ∀ i : ℕ+, ∀ j k : ℕ+, j ≤ k → k < i →
  a i ≠ (Finset.Icc j k).sum a

variable (a : ℕ+ ↪o ℕ) (h1 : IsNNeg a) (h2 : IsNotSum a)

open Asymptotics Filter Topology

include h1

include h2 in
/-- The first conjecture of Erdős problem 839: The sequence `a` grows super-linearly
in the sense that the limit superior of $a_n / n$ is infinite.-/
theorem erdos_839_1 :
  limsup (fun n ↦ (a n / n : ENNReal)) atTop = ⊤ := sorry

lemma a_incr (i : ℕ+) : i ≤ a i := by
  induction i
  · exact h1
  · expose_names
    have : a n < a (n + 1) :=
      (OrderEmbedding.lt_iff_lt a).mpr <| PNat.lt_add_right n 1
    change n.1.succ ≤ a (n + 1)
    refine Nat.succ_le_of_lt <| Nat.lt_of_le_of_lt h this

/-- The set of indices `i` such that `a_i` is strictly less than real number `x`.
Used to define the partial sum of reciprocals. -/
def sumSet (x : NNReal) := {i | a i < ⌊x⌋₊}

/-- Proof that `sumSet a x` is finite for any real `x`, given that `a` is strictly increasing.-/
def sumFin (x : NNReal) : (sumSet a x).Finite := by
  have : sumSet a x ⊆ {i | i < ⌊x⌋₊} := by
    simp [sumSet]
    intro i hi
    exact Nat.lt_of_le_of_lt (a_incr a h1 i) hi
  refine Set.Finite.subset ?_ this
  refine Set.Finite.of_surjOn Nat.toPNat' (s := {i | i < ⌊x⌋₊}) ?_ ?_
  · intro i hi
    simp at hi ⊢
    use i, hi, PNat.coe_toPNat' i
  exact Set.finite_lt_nat ⌊x⌋₊

noncomputable def sumFinset (x : NNReal) : Finset ℕ+ :=
  Set.Finite.toFinset (sumFin a h1 x)

/-- The partial sum of the reciprocals of terms in `a` strictly less than `x`.
defined as $\sum_{a_n < x} \frac{1}{a_n}$.-/
noncomputable def sumOf (x : NNReal) : ℝ :=
  (sumFinset a h1 x).sum (fun i ↦ 1 / (a i : ℝ))

include h2 in
/-- The second conjecture of Erdős problem 839: The logarithmic density of the sequence
is zero. Specifically, the quantity $\frac{1}{\log x} \sum_{a_n < x} \frac{1}{a_n}$ tends to
0 as $x \to \infty$.-/
theorem erdos_839_2 :
  Tendsto (fun x : NNReal ↦ (1 / Real.log x) * (sumOf a h1 x)) atTop (𝓝 0) := sorry
