/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# A cut witnessing many collisions

A spanning forest has the same nonisolated vertices as the original graph.
Its two-coloring gives a cut across which every nonisolated vertex has a
neighbor. At least half of any specified set of nonisolated vertices lie on
one side of this cut. Restricting that side to the specified vertices keeps
all its witnesses outside the chosen set.

For the scheduler, vertices are requests together with an occupied-set
vertex. Conditioning on directions outside the selected requests then makes
their collision tests independent. No independence of graph edges is needed.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

/-- A finite set of nonisolated vertices contains a subset of at least half
its cardinality whose vertices all have neighbors outside the subset. -/
theorem existsCollisionCut
    {Vertex : Type*}
    (graph : SimpleGraph Vertex) (bad : Finset Vertex)
    (nonisolated : ∀ vertex ∈ bad, ∃ neighbor, graph.Adj vertex neighbor) :
    ∃ selected : Finset Vertex, selected ⊆ bad ∧
      bad.card ≤ 2 * selected.card ∧
      ∀ vertex ∈ selected, ∃ neighbor,
        neighbor ∉ selected ∧ graph.Adj vertex neighbor := by
  classical
  obtain ⟨forest, forestLe, acyclic, reachable⟩ :=
    graph.exists_isAcyclic_reachable_eq_le
  let coloring := acyclic.coloringTwo
  have oppositeNeighbor (vertex : Vertex) (vertexBad : vertex ∈ bad) :
      ∃ neighbor, coloring vertex ≠ coloring neighbor ∧
        graph.Adj vertex neighbor := by
    obtain ⟨other, adjacent⟩ := nonisolated vertex vertexBad
    have forestReachable : forest.Reachable vertex other := by
      rw [reachable]
      exact adjacent.reachable
    have supported := SimpleGraph.mem_support_of_reachable adjacent.ne forestReachable
    obtain ⟨neighbor, neighborAdjacent⟩ := (SimpleGraph.mem_support forest).mp supported
    exact ⟨neighbor, coloring.valid neighborAdjacent, forestLe neighborAdjacent⟩
  let left := bad.filter fun vertex => coloring vertex = 0
  let right := bad.filter fun vertex => coloring vertex ≠ 0
  have partition : left.card + right.card = bad.card :=
    Finset.card_filter_add_card_filter_not (s := bad) _
  have cutWorks (selected : Finset Vertex)
      (selectedBad : selected ⊆ bad)
      (sameColor : ∀ vertex ∈ selected, ∀ other ∈ selected,
        coloring vertex = coloring other) :
      ∀ vertex ∈ selected, ∃ neighbor,
        neighbor ∉ selected ∧ graph.Adj vertex neighbor := by
    intro vertex vertexSelected
    obtain ⟨neighbor, opposite, adjacent⟩ :=
      oppositeNeighbor vertex (selectedBad vertexSelected)
    refine ⟨neighbor, ?_, adjacent⟩
    intro neighborSelected
    exact opposite (sameColor vertex vertexSelected neighbor neighborSelected)
  by_cases leftLarge : right.card ≤ left.card
  · refine ⟨left, Finset.filter_subset _ _, by omega, cutWorks left
      (Finset.filter_subset _ _) ?_⟩
    intro vertex vertexLeft other otherLeft
    exact (Finset.mem_filter.mp vertexLeft).2.trans
      (Finset.mem_filter.mp otherLeft).2.symm
  · refine ⟨right, Finset.filter_subset _ _, by omega, cutWorks right
      (Finset.filter_subset _ _) ?_⟩
    intro vertex vertexRight other otherRight
    have vertexNonzero := (Finset.mem_filter.mp vertexRight).2
    have otherNonzero := (Finset.mem_filter.mp otherRight).2
    exact Fin.ext (by
      have := (coloring vertex).isLt
      have := (coloring other).isLt
      have : (coloring vertex).val ≠ 0 := by simpa using vertexNonzero
      have : (coloring other).val ≠ 0 := by simpa using otherNonzero
      omega)

end Algebraic.MassProduction.Nonuniform
