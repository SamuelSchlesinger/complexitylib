/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AndOr
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# The monotone Boolean CLIQUE function

This file fixes a concrete, one-variable-per-undirected-edge encoding of
`CLIQUE`.  Edges are ordered pairs `(u,v)` with `u < v`; the noncomputable
equivalence with `Fin (Fintype.card (Edge n))` is only the boundary required
by `Circuit`'s `Fin`-indexed input interface.

Two finite test families are provided for the approximation argument:

* `CliqueSet n k`, the `k`-subsets of the vertex set, represented by their
  minimal positive graphs; and
* `Coloring n r`, whose assignments are complete `r`-partite graphs.

For `r = k - 1`, every coloring assignment is a negative CLIQUE input.  This
is the pigeonhole separation used in Razborov's monotone approximation
method.
-/

@[expose] public section

namespace Algebraic
namespace Monotone
namespace Clique

noncomputable section

/-- A canonical undirected edge on `Fin n`. -/
abbrev Edge (n : Nat) := { edge : Fin n × Fin n // edge.1 < edge.2 }

noncomputable instance : Fintype (Edge n) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun edge : Fin n × Fin n => edge.1 < edge.2)
    (by simp)

/-- The number of undirected edges in the chosen encoding. -/
abbrev edgeCount (n : Nat) := Fintype.card (Edge n)

/-- Reindex canonical edges by the `Fin` input type expected by circuits. -/
def edgeEquiv (n : Nat) : Edge n ≃ Fin (edgeCount n) :=
  Fintype.equivFin _

/-- Both endpoints of an edge lie in a vertex set. -/
def Edge.Inside (edge : Edge n) (vertices : Finset (Fin n)) : Prop :=
  edge.1.1 ∈ vertices ∧ edge.1.2 ∈ vertices

instance (edge : Edge n) (vertices : Finset (Fin n)) :
    Decidable (edge.Inside vertices) := by
  unfold Edge.Inside
  infer_instance

/-- The family of `k`-element vertex sets. -/
abbrev CliqueSet (n k : Nat) :=
  ↥((Finset.univ : Finset (Fin n)).powersetCard k)

/-- The family of vertex colorings with `r` colors. -/
abbrev Coloring (n r : Nat) := Fin n → Fin r

/-- The minimal positive graph consisting exactly of the edges induced by a
vertex set. -/
def cliqueAssignment
    (vertices : Finset (Fin n)) : Fin (edgeCount n) → Bool :=
  by
    classical
    exact fun input =>
      decide (Edge.Inside ((edgeEquiv n).symm input) vertices)

@[simp] theorem cliqueAssignment_edge
    (vertices : Finset (Fin n))
    (edge : Edge n) :
    cliqueAssignment vertices (edgeEquiv n edge) =
      decide (edge.Inside vertices) := by
  classical
  simp [cliqueAssignment]

/-- The complete multipartite graph induced by a coloring: vertices are
adjacent exactly when they receive different colors. -/
def coloringAssignment
    (coloring : Coloring n r) : Fin (edgeCount n) → Bool :=
  by
    classical
    exact fun input =>
      let edge := (edgeEquiv n).symm input
      decide (coloring edge.1.1 ≠ coloring edge.1.2)

@[simp] theorem coloringAssignment_edge
    (coloring : Coloring n r)
    (edge : Edge n) :
    coloringAssignment coloring (edgeEquiv n edge) =
      decide (coloring edge.1.1 ≠ coloring edge.1.2) := by
  simp [coloringAssignment]

/-- An assignment contains every edge induced by `vertices`. -/
def Contains
    (assignment : Fin (edgeCount n) → Bool)
    (vertices : Finset (Fin n)) : Prop :=
  ∀ edge : Edge n, edge.Inside vertices →
    assignment (edgeEquiv n edge) = true

/-- Containing the clique on a vertex set implies containing every smaller
clique. -/
theorem Contains.mono_vertices
    {assignment : Fin (edgeCount n) → Bool}
    {small large : Finset (Fin n)}
    (subset : small ⊆ large)
    (contains : Contains assignment large) :
    Contains assignment small := by
  intro edge inside
  exact contains edge ⟨subset inside.1, subset inside.2⟩

/-- On a minimal clique graph, every contained vertex set of size at least two
lies inside the generating clique. -/
theorem subset_of_contains_cliqueAssignment
    {vertices test : Finset (Fin n)}
    (two_le : 2 ≤ test.card)
    (contains : Contains (cliqueAssignment vertices) test) :
    test ⊆ vertices := by
  classical
  intro vertex vertexPresent
  have erasedNonempty : (test.erase vertex).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem vertexPresent]
    omega
  obtain ⟨other, otherPresentErased⟩ := erasedNonempty
  have otherPresent : other ∈ test := Finset.mem_of_mem_erase otherPresentErased
  have different : vertex ≠ other := by
    exact fun equal => (Finset.ne_of_mem_erase otherPresentErased) equal.symm
  rcases lt_or_gt_of_ne different with before | after
  · let edge : Edge n := ⟨(vertex, other), before⟩
    have edgePresent := contains edge ⟨vertexPresent, otherPresent⟩
    rw [cliqueAssignment_edge, decide_eq_true_eq] at edgePresent
    exact edgePresent.1
  · let edge : Edge n := ⟨(other, vertex), after⟩
    have edgePresent := contains edge ⟨otherPresent, vertexPresent⟩
    rw [cliqueAssignment_edge, decide_eq_true_eq] at edgePresent
    exact edgePresent.2

instance (assignment : Fin (edgeCount n) → Bool)
    (vertices : Finset (Fin n)) : Decidable (Contains assignment vertices) :=
  by
    classical
    exact Fintype.decidableForallFintype

/-- The ordinary monotone Boolean `k`-CLIQUE function on `n` vertices. -/
def function (n k : Nat) (assignment : Fin (edgeCount n) → Bool) : Bool :=
  decide (∃ vertices : CliqueSet n k,
    Contains assignment vertices.1)

/-- The minimal graph of a `k`-set is a positive CLIQUE input. -/
@[simp] theorem function_cliqueAssignment
    (vertices : CliqueSet n k) :
    function n k (cliqueAssignment vertices.1) = true := by
  rw [function, decide_eq_true_eq]
  refine ⟨vertices, ?_⟩
  intro edge inside
  simp [cliqueAssignment_edge, inside]

/-- If a coloring graph contains a clique on `vertices`, then the coloring is
injective on those vertices. -/
theorem coloring_injectiveOn_of_contains
    (coloring : Coloring n r)
    (vertices : Finset (Fin n))
    (contains : Contains (coloringAssignment coloring) vertices) :
    Set.InjOn coloring ↑vertices := by
  intro left leftPresent right rightPresent colorsEqual
  by_contra verticesDifferent
  have ordered : left < right ∨ right < left := lt_or_gt_of_ne verticesDifferent
  rcases ordered with leftBeforeRight | rightBeforeLeft
  · let edge : Edge n := ⟨(left, right), leftBeforeRight⟩
    have present := contains edge ⟨leftPresent, rightPresent⟩
    rw [coloringAssignment_edge, decide_eq_true_eq] at present
    exact present colorsEqual
  · let edge : Edge n := ⟨(right, left), rightBeforeLeft⟩
    have present := contains edge ⟨rightPresent, leftPresent⟩
    rw [coloringAssignment_edge, decide_eq_true_eq] at present
    exact present colorsEqual.symm

/-- A complete `r`-partite graph has no clique larger than its color set. -/
theorem card_le_colors_of_contains_coloring
    (coloring : Coloring n r)
    (vertices : Finset (Fin n))
    (contains : Contains (coloringAssignment coloring) vertices) :
    vertices.card ≤ r := by
  let restricted : ↥vertices → Fin r := fun vertex => coloring vertex.1
  have injective : Function.Injective restricted := by
    intro left right equal
    apply Subtype.ext
    exact coloring_injectiveOn_of_contains coloring vertices contains
      left.2 right.2 equal
  have cardinality := Fintype.card_le_of_injective restricted injective
  simpa using cardinality

/-- Every complete `(k-1)`-partite graph is a negative `k`-CLIQUE input. -/
theorem function_coloringAssignment_eq_false
    (positive : 0 < k)
    (coloring : Coloring n (k - 1)) :
    function n k (coloringAssignment coloring) = false := by
  rw [function, decide_eq_false_iff_not]
  rintro ⟨vertices, contains⟩
  have bounded := card_le_colors_of_contains_coloring coloring vertices.1 contains
  have cardinality : vertices.1.card = k :=
    (Finset.mem_powersetCard.mp vertices.2).2
  omega

/-- CLIQUE is monotone in its edge variables. -/
theorem function_monotone : Monotone (function n k) := by
  intro lower upper below
  simp only [function]
  intro accepted
  rw [decide_eq_true_eq] at accepted ⊢
  rcases accepted with ⟨vertices, contains⟩
  refine ⟨vertices, ?_⟩
  intro edge inside
  have lowerTrue := contains edge inside
  have ordered := below (edgeEquiv n edge)
  apply Bool.eq_true_of_true_le
  simpa [lowerTrue] using ordered

end

end Clique
end Monotone
end Algebraic
