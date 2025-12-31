import Mathlib

open Classical Asymptotics Filter

/-
- `Fin n → ℝ`：n维向量
- `Set (Fin n → ℝ)`：几何体（一堆向量的集合）
- `Set.Icc (0 : Fin n → ℝ) 1`：n维单位立方体，`Fin n → ℝ`上的`Preorder`为`Pi.preorder`，
  所以`Set.Icc (0 : Fin n → ℝ) 1`就是
    {v : Fin n → ℝ | 0 ≤ v ≤ 1} = {v | ∀ i, 0 ≤ vᵢ ≤ 1}
  相应地，`Set.Icc (a : Fin n → ℝ) b`就是{v | ∀ i, aᵢ ≤ vᵢ ≤ bᵢ}
-/

/-- 定义在一个n维空间中，一个集合是否为homothetic n-dimensional cubes（即位似立方体）.-/
def IsHomotheticCube (n : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  -- 这里的a就是位似立方体的左下顶点（每个坐标的最小值）
  ∃ (a : Fin n → ℝ) (s : ℝ), s > 0 ∧
    -- `(a + fun _ ↦ s)`是右上顶点（每个坐标分量都是aᵢ+s）
    -- 因此`Set.Icc a (a + fun _ ↦ s)`就是{v | ∀ i, aᵢ ≤ v ≤ aᵢ + s}，也即以a为左下顶点的边长为s的立方体
    S = Set.Icc a (a + fun _ ↦ s)

/-- 定义一个正整数k是否能剖分n维单位立方体.-/
def CanDecompose (n : ℕ) (k : ℕ) : Prop :=
  -- 存在k个几何体
  ∃ (C : Fin k → Set (Fin n → ℝ)),
    -- 1. 每一个都是位似立方体
    (∀ i, IsHomotheticCube n (C i)) ∧
    -- 2. 它们并起来是整个单位立方体
    (⋃ i, C i = Set.Icc 0 1) ∧
    -- 3. 它们内部互不相交（测度论角度：交集的测度为 0）
    (∀ i j, i ≠ j → MeasureTheory.volume (C i ∩ C j) = 0)

/-- 定义c(n)为最小的临界值.-/
noncomputable def c (n : ℕ) : ℕ :=
  if h : ∃ n₀, ∀ k ≥ n₀, CanDecompose n k
    then Nat.find h
  else 0

/-- Erdős的猜想：c(n) >> n^n.-/
theorem erdos_769 : (fun n : ℕ ↦ (n ^ n : ℝ)) =O[atTop] (fun n ↦ (c n : ℝ)) := sorry
