import Mathlib

/- Let $A$ be the set of $n \in \mathbb{N}$ such that there exist
$1\leq m_1< \cdots < m_k=n$ with $\sum\tfrac{1}{m_i}=1$.
$A$ have density $1$.-/

/-
1. In formalization, we usually interpret sequence $m_1 \cdots m_k$ as a map
from $\{1, \cdots, k\}$ to $\mathbb{N}$. Here I use `Finset.Icc 1 k` to
represent $\{1, \cdots, k\}$.
2. $m_1 < \cdots < m_k$ is ensured by `StrictMono`
3. all properties of $m$, including $1\leq m_1< \cdots < m_k=n$ and
$\sum\tfrac{1}{m_i}=1$, are encoded in `m_prop`.
-/

/-- Give $1 \leq k$ and a natural number $n$, a desired $m$ would be a strictly
monotone map from $\{1, \cdots, k\}$ to $\mathbb{N}$ such that $1 \leq m_1$,
$m_k = n$, with $\sum\tfrac{1}{m_i}=1$.-/
abbrev m_prop {k : ℕ+} (n : ℕ) (m : Finset.Icc 1 k → ℕ) : Prop :=
  -- $m$ is strictly monotone. This is to ensure $m_1< \cdots < m_k$
  StrictMono m ∧
  -- $1\leq m_1$
  1 ≤ m ⟨1, Finset.left_mem_Icc.mpr k.2⟩ ∧
  -- $m_k = n$
  m ⟨k, Finset.right_mem_Icc.mpr k.2⟩ = n ∧
  -- $\sum\tfrac{1}{m_i}=1$
  ∑ i, (1 / m i : ℚ) = 1

/-- $A$ is the set of $n \in \mathbb{N}$ such that there exist a natural
number $1 \leq k$ and a strictly monotone sequence $1\leq m_1< \cdots < m_k=n$ with $\sum\tfrac{1}{m_i}=1$.-/
abbrev A : Set ℕ :=
  {n : ℕ | ∃ k : ℕ+, ∃ m : Finset.Icc 1 k → ℕ, m_prop n m}

open Classical in
/-- $A$ has density 1.-/
theorem erdos292 : schnirelmannDensity A = 1 := sorry

section testflight

#check schnirelmannDensity

variable {k : ℕ+}

variable (m : Finset.Icc 1 k →o ℕ)
  (hm : Function.Injective m)

example (i j : Finset.Icc 1 k) (h : i < j) : m i < m j :=
  Nat.lt_of_le_of_ne (m.monotone (Std.le_of_lt h))
    (fun hx ↦ (ne_of_lt h) (hm hx))

example : 1 ∈ Finset.Icc 1 k := Finset.left_mem_Icc.mpr k.2
example : k ∈ Finset.Icc 1 k := Finset.right_mem_Icc.mpr k.2

#check m ⟨1, Finset.left_mem_Icc.mpr k.2⟩
#check m ⟨k, Finset.right_mem_Icc.mpr k.2⟩

#check ∑ i, (1 / m i : ℚ)

#check (Finset.Icc 1 k).toList

end testflight
