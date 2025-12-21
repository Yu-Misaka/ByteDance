import Mathlib

open Asymptotics Filter

/--
特定N下的匹配保证：这个谓词定义了题目中最核心的“存在性”结构。即对于固定的N和m，数值r是一个“可行的匹配数量”。

- N : 题目中的大N（决定全集范围和区间长度）。
- m : 集合A的大小。
- r : 我们声称能找到的匹配数量（即题干中的 "many distinct integers" 的数量）。
-/
def GuaranteedMatch (N : ℕ+) (m : ℕ) (r : ℕ) : Prop :=
  -- "if A ⊆ {1...N} has |A|=m"
  ∀ (A : Finset ℕ+), A ⊆ Finset.Icc 1 N → A.card = m →
    -- "every interval in [1, ∞) of length 2N"
    ∀ (x : ℕ+),
      -- Ico(a, b) 长度为 b-a = 2N
      let I := Finset.Ico x (x + 2 * N)
      -- "contains ≥ f(m) (here r) many distinct integers b_i where each b_i is divisible by distinct a_i"
      -- 这里单射`↪`保证了distinct
      ∃ (b : Fin r ↪ I) (a : Fin r ↪ A),
        ∀ i : Fin r, (a i : ℕ) ∣ (b i : ℕ)

/--
函数f的性质：原题说 "Let f(m) be such that..."，这意味着f(m)是一个通用的下界。
最关键的是f(m)不能依赖于N。它必须对任意足够大的N都成立。也即：
对于一个固定的m，无论N变得多大（只要N能容纳大小为m的集合A，即m≤N），f(m)个匹配都必须能被保证。
-/
def IsValidErdosBound (f : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, ∀ N : ℕ+, m ≤ N → GuaranteedMatch N m (f m)

/--
Let f(m) be such that if A ⊆ {1...N} has |A|=m, then every interval in [1, ∞)
of length 2N contains ≥ f(m) many distinct integers b_i divisible by distinct a_i ∈ A.
Then f(m) ≪ m^(1/2).
-/
theorem erdos_650 :
  ∀ (f : ℕ → ℕ), IsValidErdosBound f →
    (fun m ↦ (f m : ℝ)) =O[atTop] (fun m ↦ Real.sqrt m) := by
  sorry
