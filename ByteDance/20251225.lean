import Mathlib

/--
The set of values $\gcd(n, \binom{n}{k})$ where $1 < k \le n/2$.
-/
abbrev map_set (n : ℕ) : Finset ℕ :=
  (Finset.Ioc 1 (n / 2)).image (fun k ↦ Nat.gcd n (Nat.choose n k))

/--
For $n \ge 4$, the range $(1, n/2]$ is nonempty, and thus `map_set n` is nonempty.
-/
lemma map_set_nonempty {n : ℕ} (hn : 4 ≤ n) :
    (map_set n).Nonempty := by
  simp only [Finset.image_nonempty, Finset.nonempty_Ioc]
  omega

/--
The function $f(n) = \min_{1 < k \le n/2} \gcd(n, \binom{n}{k})$.
Defined as the minimum of `map_set n`. Returns 0 if $n < 4$.
-/
def f (n : ℕ) : ℕ :=
  if hn : 4 ≤ n then
    (map_set n).min' (map_set_nonempty hn)
  else 0

/--
A natural number is composite if it is greater than 1 and not prime.
-/
def Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/--
The condition $f(n) = n / P(n)$, where $P(n)$ is the largest prime factor of $n$.
This predicate is used in the first question of Erdős Problem 700.
-/
def erdos_condition {n : ℕ} (hn : 1 < n) : Prop :=
  f n = n / n.primeFactors.max'
    (Nat.nonempty_primeFactors.2 hn)

/--
Erdős Problem 700 (i):
There exists a structural property `P` characterizing the composite numbers `n`
that satisfy the condition $f(n) = n / P(n)$.
-/
theorem erdos_700_1 :
  ∃ (P : ℕ → Prop), ∀ n, (hn : n.Composite) →
    (erdos_condition hn.1 ↔ P n) := sorry

/--
Erdős Problem 700 (ii):
The set of composite numbers $n$ such that $f(n) > \sqrt{n}$ is infinite.
-/
theorem erdos_700_2 :
  {n : ℕ | n.Composite ∧ Real.sqrt n < f n}.Infinite := sorry

/--
Erdős Problem 700 (iii):
For every $A > 0$, the function $f(n)$ is bounded by $O_A(n / (\log n)^A)$.
Explicitly, there exists a constant $C$ such that $f(n) \le C \frac{n}{(\log n)^A}$
for sufficiently large composite $n$.
-/
theorem erdos_700_3 : ∀ (A : ℝ), A > 0 →
  ∃ (C : ℝ), C > 0 ∧
    ∃ (N : ℕ), ∀ (n : ℕ), n > N → n.Composite →
      (f n : ℝ) ≤ C * (n / (Real.log n) ^ A) := sorry
