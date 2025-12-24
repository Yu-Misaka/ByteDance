import Mathlib

open Classical Filter Topology

/--
Calculates the proportion of elements of `S` in the range `1` to `n`.
That is: $\frac{|S \cap \{1..n\}|}{n}$.
-/
noncomputable def f (S : Set ℕ) : ℕ → ℝ :=
  fun n ↦ (Nat.card (S ∩ Finset.Icc 1 n : Set ℕ) : ℝ) / n

/--
The natural density of a set `S`, defined here as the **Upper Density**.

Why use `limsup`? In this formalization, natural density is defined as $\limsup_{n \to \infty} \frac{|S \cap \{1..n\}|}{n}$ for the following reasons:

- For any set that possesses a natural density, its upper density is strictly equal to its natural density. Thus, conditioned on the limit existing, this definition coincides with the standard definition.

- The sets involved in this problem are of the form $\{x : \exists d \in D, d \mid x\}$ where $D$ is a finite set
(determined by the bounds $1 < d < \exp(m^\alpha)$).
Such a set is a union of finitely many arithmetic progressions (multiples).
It is a standard number-theoretic result that the natural density for such sets **always exists**.
Therefore, using `limsup` here is purely a formal convenience; in the context of this problem,
it is mathematically equivalent to the actual limit.
-/
noncomputable def naturalDensity (S : Set ℕ) : ℝ :=
  limsup (f S) atTop

/--
The density function $\delta(m, \alpha)$ as defined in Erdős Problem 697.

It represents the natural density of the set of integers $x$ that have a divisor $d$ satisfying:
1. $d \equiv 1 \pmod m$
2. $1 < d < \exp(m^\alpha)$
3. $d \mid x$
-/
noncomputable def δ (m : ℕ) (α : ℝ) : ℝ :=
  naturalDensity
    {x : ℕ | ∃ d : ℕ, d ≡ 1 [MOD m] ∧ 1 < d ∧ d < Real.exp (m ^ α) ∧ d ∣ x}

/--
Formal Statement of Erdős Problem 697:
There exists a critical value $\beta \in (1, \infty)$ such that:
* If $\alpha < \beta$, the density $\delta(m, \alpha)$ tends to 0 as $m \to \infty$.
* If $\alpha > \beta$, the density $\delta(m, \alpha)$ tends to 1 as $m \to \infty$.
-/
theorem erdos_697 : ∃ β : ℝ, 1 < β ∧ ∀ α : ℝ,
  (α < β → Tendsto (fun m ↦ δ m α) atTop (𝓝 0)) ∧
  (β < α → Tendsto (fun m ↦ δ m α) atTop (𝓝 1)) := sorry
