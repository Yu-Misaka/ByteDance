import Mathlib

open Pointwise Asymptotics Filter

/-- sequence that satisfies the condition of erdos problem 1103.

"an infinite sequence of integers" is formalized as a strict monotone
map from `ℕ` to `ℤ`, where the entrance denotes index.

(Since we are discussing the growth rate of `A`, this sequence should be monotone.
And the problem would become trivial if we allow sequence like "1, 1, 1, ...", so we
demand a strict monotone one). -/
def erdos_1103_prop (A : ℕ ↪o ℤ) : Prop :=
  ∀ n ∈ (Set.range A + Set.range A), Squarefree n

/-- Let $A$ be an infinite sequence of integers such that every $n\in A+A$ is squarefree.
How fast must $A$ grow?-/
theorem erdos_1103 {A : ℕ ↪o ℤ} (hA : erdos_1103_prop A) :
  ∃ l : ℕ → ℝ, l =O[atTop] (fun x ↦ (A x : ℝ)) := sorry
