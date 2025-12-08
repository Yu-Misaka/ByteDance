import Mathlib

open Filter

/--
A structure representing a 3-uniform hypergraph.
It consists of a collection of edges, where each edge is a set of exactly 3 vertices.
-/
structure ThreeUniformHypergraph (α : Type*) [DecidableEq α] where
  /-- The set of edges in the hypergraph. Each edge is a finite set of vertices. -/
  edges : Finset (Finset α)
  /-- Uniformity condition: Every edge must contain exactly 3 vertices. -/
  uniform : ∀ e ∈ edges, e.card = 3

variable {α : Type*} [DecidableEq α] [Fintype α]

/--
Predicate determining if a 3-uniform hypergraph is a Steiner Triple System (STS).
An STS requires that every pair of distinct vertices is contained in exactly one edge.
-/
def is_steiner_triple_system (H : ThreeUniformHypergraph α) : Prop :=
  ∀ x y : α, x ≠ y → ∃! e ∈ H.edges, x ∈ e ∧ y ∈ e

/--
Predicate checking if the hypergraph has "high girth" (sparse property) up to parameter `g`.
Specifically, for any number of edges `j` (where `2 ≤ j ≤ g`), the union of these `j` edges
must span at least `j + 3` distinct vertices.
-/
def has_high_girth (H : ThreeUniformHypergraph α) (g : ℕ) : Prop :=
  ∀ j : ℕ, 2 ≤ j ∧ j ≤ g →
    ∀ (sub_edges : Finset (Finset α)),
      sub_edges ⊆ H.edges → sub_edges.card = j →
        (sub_edges.biUnion id).card ≥ j + 3

/--
Erdős Problem 207:
For any `g ≥ 2`, for all sufficiently large `n` satisfying the admissibility condition
(`n ≡ 1` or `3 mod 6`), there exists a 3-uniform hypergraph on `n` vertices that is
both a Steiner Triple System and has high girth `g`.
-/
theorem erdos_207 : ∀ g ≥ 2, ∀ᶠ n in atTop,
  n ≡ 1 [MOD 6] ∨ n ≡ 3 [MOD 6] →
    ∃ H : ThreeUniformHypergraph (Fin n),
      is_steiner_triple_system H ∧ has_high_girth H g := sorry
