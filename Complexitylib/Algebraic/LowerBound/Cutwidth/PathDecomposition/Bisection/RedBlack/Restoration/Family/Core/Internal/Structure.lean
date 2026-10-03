/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions.Defs

/-!
# Core pieces of a restoration family

Restoring only some region boundaries preserves the graph obtained by deleting
all boundaries. Its surviving core pieces are disjoint from every region.
Every edge in the suppressed core graph passes through one region vertex,
since distinct surviving pieces have no direct edge in the boundary quotient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι)

theorem deletedGraph_le_restrict (indices : Finset ι) :
    F.deletedGraph ≤ (F.restrict indices).deletedGraph := by
  apply B.deleteEdges_anti
  intro e he
  change e ∈ (F.restrict indices).deletedEdges at he
  rw [deletedEdges_restrict] at he
  obtain ⟨i, _, member⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, member⟩

theorem delete_region_cuts_eq (H : SimpleGraph V)
    (kept : F.deletedGraph ≤ H) (original : H ≤ B) :
    H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V))) = F.deletedGraph := by
  ext u v
  rw [deletedGraph, SimpleGraph.deleteEdges_adj, SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨adjacent, fresh⟩
    refine ⟨original adjacent, ?_⟩
    intro removed
    obtain ⟨i, _, crossing⟩ := Finset.mem_biUnion.mp removed
    exact fresh (Set.mem_iUnion.mpr ⟨i, H.mem_cutFinset_mk.mpr
      ⟨adjacent, (B.mem_cutFinset_mk.mp crossing).2⟩⟩)
  · rintro ⟨adjacent, fresh⟩
    refine ⟨kept (SimpleGraph.deleteEdges_adj.mpr ⟨adjacent, fresh⟩), ?_⟩
    intro removed
    obtain ⟨i, crossing⟩ := Set.mem_iUnion.mp removed
    exact fresh (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      B.mem_cutFinset_mk.mpr ⟨adjacent, (H.mem_cutFinset_mk.mp crossing).2⟩⟩)

variable (H : SimpleGraph V)
  (f : ι ↪ (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent)
  (support : ∀ i, (f i).supp.toFinset = F.region i)

include support

theorem core_disjoint_region (u : {C // C ∉ Finset.univ.image f}) (i : ι) :
    Disjoint u.val.supp.toFinset (F.region i) := by
  apply Finset.disjoint_left.mpr
  intro a ha hi
  have inRegion : a ∈ (f i).supp := by
    apply Set.mem_toFinset.mp
    rwa [support]
  have same := SimpleGraph.ConnectedComponent.eq_of_common_vertex
    inRegion (Set.mem_toFinset.mp ha)
  exact u.property (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, same⟩)

private theorem core_not_adj (u v : {C // C ∉ Finset.univ.image f}) :
    ¬ (BridgeQuotient.ofRegions H F.region).Adj u.val v.val := by
  rintro ⟨different, a, ha, b, hb, adjacent⟩
  have retained :
      (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).Adj a b := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨adjacent, ?_⟩
    intro removed
    obtain ⟨i, crossing⟩ := Set.mem_iUnion.mp removed
    rcases (H.mem_cutFinset_mk.mp crossing).2 with ⟨hi, _⟩ | ⟨hi, _⟩
    · exact Finset.disjoint_left.mp (core_disjoint_region F H f support u i)
        (Set.mem_toFinset.mpr ha) hi
    · exact Finset.disjoint_left.mp (core_disjoint_region F H f support v i)
        (Set.mem_toFinset.mpr hb) hi
  exact different (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (u.val.mem_supp_of_adj_mem_supp ha retained) hb)

theorem core_adj_iff_exists_region (u v : {C // C ∉ Finset.univ.image f}) :
    (PathSuppression.coreGraph H F.region f).Adj u v ↔
      u ≠ v ∧ ∃ i, (BridgeQuotient.ofRegions H F.region).Adj u.val (f i) ∧
        (BridgeQuotient.ofRegions H F.region).Adj (f i) v.val := by
  constructor
  · rintro ⟨different, direct | ⟨C, member, first, second⟩⟩
    · exact (core_not_adj F H f support u v direct).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
      exact ⟨different, i, first, second⟩
  · rintro ⟨different, i, first, second⟩
    exact ⟨different, Or.inr ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      first, second⟩⟩

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal
