/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal.Rank
import Mathlib.Data.Finset.Max

/-!
# Removing designated edges from cycles

Choose a largest set of designated edges whose deletion preserves
reachability. Every remaining designated edge is then a bridge. The
number removed is bounded by the original cycle rank, since the surviving
graph still has the same connected components.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

private theorem card_vertices_le_edges_add_components :
    Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent := by
  simpa using card_vertices_add_cyclic_le B ∅ (by simp)

theorem exists_delete_to_bridges (eligible : Finset (Sym2 V)) (edges : eligible ⊆ B.edgeFinset) :
    ∃ removed ⊆ eligible,
      (B.deleteEdges (removed : Set (Sym2 V))).Reachable = B.Reachable ∧
      (∀ e ∈ eligible \ removed, (B.deleteEdges (removed : Set (Sym2 V))).IsBridge e) ∧
      removed.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent := by
  let candidates := eligible.powerset.filter
    (fun removed : Finset (Sym2 V) =>
      (B.deleteEdges (removed : Set (Sym2 V))).Reachable = B.Reachable)
  have nonempty : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    simp
  obtain ⟨removed, member, maximal⟩ := candidates.exists_max_image Finset.card nonempty
  have subset := Finset.mem_powerset.mp (Finset.mem_filter.mp member).1
  have reachable := (Finset.mem_filter.mp member).2
  refine ⟨removed, subset, reachable, ?_, ?_⟩
  · intro e he
    have allowed := (Finset.mem_sdiff.mp he).1
    have fresh := (Finset.mem_sdiff.mp he).2
    by_contra notBridge
    have step : B.deleteEdges ((insert e removed : Finset (Sym2 V)) : Set (Sym2 V)) =
        (B.deleteEdges (removed : Set (Sym2 V))).deleteEdges {e} := by
      rw [SimpleGraph.deleteEdges_deleteEdges]
      congr 1
      ext f
      simp
    have newReachable :
        (B.deleteEdges ((insert e removed : Finset (Sym2 V)) : Set (Sym2 V))).Reachable =
        B.Reachable := by
      rw [step]
      funext u v
      apply propext
      constructor
      · intro h
        exact (h.mono (SimpleGraph.deleteEdges_le _)).mono (SimpleGraph.deleteEdges_le _)
      · intro h
        have old : (B.deleteEdges (removed : Set (Sym2 V))).Reachable u v := by
          rw [reachable]
          exact h
        exact old.reachable_deleteEdges_of_not_isBridge notBridge
    have newMember : insert e removed ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset allowed subset), newReachable⟩
    have bound := maximal (insert e removed) newMember
    rw [Finset.card_insert_of_notMem fresh] at bound
    lia
  · have lower := card_vertices_le_edges_add_components (B.deleteEdges (removed : Set (Sym2 V)))
    have components : Nat.card (B.deleteEdges (removed : Set (Sym2 V))).ConnectedComponent =
        Nat.card B.ConnectedComponent := by
      unfold SimpleGraph.ConnectedComponent
      rw [reachable]
    rw [components, SimpleGraph.edgeFinset_deleteEdges] at lower
    have count := Finset.card_sdiff_add_card_eq_card (subset.trans edges)
    lia

private theorem cycle_adj_of_degree_le_two {u v w : V} {p : B.Walk u u}
    (cycle : p.IsCycle) (member : v ∈ p.support) (degree : B.degree v ≤ 2)
    (adjacent : B.Adj v w) : p.toSubgraph.Adj v w := by
  have same : p.toSubgraph.neighborSet v = B.neighborSet v :=
    Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset v) (by
      rw [B.ncard_neighborSet, cycle.ncard_neighborSet_toSubgraph_eq_two member]
      exact degree)
  change w ∈ p.toSubgraph.neighborSet v
  rw [same]
  exact adjacent

theorem cycle_contains_boundary_of_meets_region {P : Finset V}
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) {u : V} {p : B.Walk u u}
    (cycle : p.IsCycle) (meets : ∃ v ∈ P, v ∈ p.support)
    {e : Sym2 V} (boundary : e ∈ B.cutFinset P) : e ∈ p.edges := by
  have propagate {a b : {v : V // v ∈ P}} (q : (B.induce {v | v ∈ P}).Walk a b) :
      a.val ∈ p.support → b.val ∈ p.support := by
    induction q with
    | nil => exact fun h => h
    | @cons a b c ab q ih =>
      intro member
      exact ih (SimpleGraph.Walk.mem_support_of_adj_toSubgraph
        (cycle_adj_of_degree_le_two B cycle member (degree a.val a.property) ab).symm)
  obtain ⟨v, hv, member⟩ := meets
  obtain ⟨adjacent, a, b, rfl, ha, _⟩ := B.mem_cutFinset.mp boundary
  obtain ⟨q⟩ := connected.preconnected ⟨v, hv⟩ ⟨a, ha⟩
  exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
    (cycle_adj_of_degree_le_two B cycle (propagate q member) (degree a ha)
      (B.mem_edgeSet.mp adjacent))

theorem exists_delete_avoiding_regions {ι : Type} [Fintype ι] (P : ι → Finset V)
    (connected : ∀ i, (B.induce {v | v ∈ P i}).Connected)
    (degree : ∀ i, ∀ v ∈ P i, B.degree v ≤ 2)
    (chosen : ι → Sym2 V) (boundary : ∀ i, chosen i ∈ B.cutFinset (P i)) :
    ∃ removed ⊆ Finset.univ.image chosen,
      (B.deleteEdges (removed : Set (Sym2 V))).Reachable = B.Reachable ∧
      removed.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent ∧
      ∀ u (p : (B.deleteEdges (removed : Set (Sym2 V))).Walk u u), p.IsCycle →
        ∀ i v, v ∈ P i → v ∉ p.support := by
  have edges : Finset.univ.image chosen ⊆ B.edgeFinset := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact B.mem_edgeFinset.mpr (B.mem_cutFinset.mp (boundary i)).1
  obtain ⟨removed, subset, reachable, bridges, size⟩ :=
    exists_delete_to_bridges B (Finset.univ.image chosen) edges
  refine ⟨removed, subset, reachable, size, ?_⟩
  intro u p cycle i v hv member
  let q := p.mapLe (SimpleGraph.deleteEdges_le _)
  have cycleQ : q.IsCycle := cycle.mapLe _
  have memberQ : v ∈ q.support := by simpa [q] using member
  have forced := cycle_contains_boundary_of_meets_region B (connected i) (degree i)
    cycleQ ⟨v, hv, memberQ⟩ (boundary i)
  have edgeP : chosen i ∈ p.edges := by simpa [q] using forced
  have present := p.edges_subset_edgeSet edgeP
  have notRemoved : chosen i ∉ removed := by
    rw [SimpleGraph.edgeSet_deleteEdges] at present
    exact present.2
  have bridge := bridges (chosen i) (Finset.mem_sdiff.mpr
    ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, notRemoved⟩)
  exact bridge.notMem_edges_of_isCycle cycle edgeP

theorem exists_isolate_regions_without_cycles {ι : Type} [Fintype ι] (P : ι → Finset V)
    (connected : ∀ i, (B.induce {v | v ∈ P i}).Connected)
    (degree : ∀ i, ∀ v ∈ P i, B.degree v ≤ 2)
    (chosen : ι → Sym2 V) (injective : Function.Injective chosen)
    (boundary : ∀ i, chosen i ∈ B.cutFinset (P i)) :
    ∃ indices : Finset ι,
      indices.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent ∧
      (B.deleteEdges (indices.image chosen : Set (Sym2 V))).Reachable = B.Reachable ∧
      ∀ u (p : (B.deleteEdges
          (indices.biUnion (fun i => B.cutFinset (P i)) : Set (Sym2 V))).Walk u u),
        p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support := by
  obtain ⟨removed, subset, reachable, size, avoids⟩ :=
    exists_delete_avoiding_regions B P connected degree chosen boundary
  let indices := Finset.univ.filter (fun i => chosen i ∈ removed)
  have image : indices.image chosen = removed := by
    ext e
    constructor
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hi).2
    · intro he
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (subset he)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  have count := Finset.card_image_of_injective indices injective
  rw [image] at count
  have extra : removed ⊆ indices.biUnion (fun i => B.cutFinset (P i)) := by
    intro e he
    rw [← image] at he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_biUnion.mpr ⟨i, hi, boundary i⟩
  have inclusion : B.deleteEdges (indices.biUnion (fun i => B.cutFinset (P i)) : Set (Sym2 V)) ≤
      B.deleteEdges (removed : Set (Sym2 V)) := by
    intro a b adjacent
    obtain ⟨original, kept⟩ := SimpleGraph.deleteEdges_adj.mp adjacent
    exact SimpleGraph.deleteEdges_adj.mpr ⟨original, fun h => kept (extra h)⟩
  refine ⟨indices, by lia, ?_, ?_⟩
  · rw [image]
    exact reachable
  · intro u p cycle i v hv
    have absent := avoids u (p.mapLe inclusion) (cycle.mapLe inclusion) i v hv
    simpa using absent

end Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal
