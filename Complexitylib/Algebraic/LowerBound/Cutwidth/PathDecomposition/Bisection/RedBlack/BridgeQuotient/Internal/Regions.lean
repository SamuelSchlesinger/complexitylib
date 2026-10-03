/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal.Core

/-!
# Identifying region vertices in the boundary quotient

Disjoint connected regions remain internally connected when any of their
boundary edges are deleted. Once all region boundaries are deleted, each
region is exactly one connected component and hence one quotient vertex.
The degree of a quotient vertex is bounded by the original cut of its
component, with equality when designated edges are bridges. These statements
identify the path vertices to be suppressed and their exact degrees.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal

open scoped Classical

variable {V ι : Type} [Fintype V] (B : SimpleGraph V) (P : ι → Finset V)

theorem induce_delete_region_cuts (disjoint : Pairwise (fun i j => Disjoint (P i) (P j)))
    (removed : Set (Sym2 V)) (subset : removed ⊆ ⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))
    (i : ι) : (B.deleteEdges removed).induce {v | v ∈ P i} = B.induce {v | v ∈ P i} := by
  ext a b
  change (B.deleteEdges removed).Adj a.val b.val ↔ B.Adj a.val b.val
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨fun h => h.1, fun ab => ⟨ab, ?_⟩⟩
  intro deleted
  obtain ⟨j, crossing⟩ := Set.mem_iUnion.mp (subset deleted)
  have crossing := (B.mem_cutFinset_mk.mp crossing).2
  by_cases same : i = j
  · rw [← same] at crossing
    rcases crossing with ⟨_, outside⟩ | ⟨_, outside⟩
    · exact outside b.property
    · exact outside a.property
  · rcases crossing with ⟨ha, _⟩ | ⟨hb, _⟩
    · exact Finset.disjoint_left.mp (disjoint same) a.property ha
    · exact Finset.disjoint_left.mp (disjoint same) b.property hb

theorem exists_region_component
    (connected : ∀ i, (B.induce {v | v ∈ P i}).Connected)
    (disjoint : Pairwise (fun i j => Disjoint (P i) (P j))) (i : ι) :
    ∃ C : (B.deleteEdges (⋃ j, (B.cutFinset (P j) : Set (Sym2 V)))).ConnectedComponent,
      C.supp.toFinset = P i := by
  let G := B.deleteEdges (⋃ j, (B.cutFinset (P j) : Set (Sym2 V)))
  obtain ⟨a⟩ := (connected i).nonempty
  let C := G.connectedComponentMk a.val
  have inside : (G.induce {v | v ∈ P i}).Connected := by
    rw [induce_delete_region_cuts B P disjoint _ (fun _ h => h) i]
    exact connected i
  have closed : G.cutFinset (P i) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨edge, u, v, rfl, hu, hv⟩ := G.mem_cutFinset.mp he
    obtain ⟨original, fresh⟩ := SimpleGraph.deleteEdges_adj.mp (G.mem_edgeSet.mp edge)
    exact fresh (Set.mem_iUnion.mpr ⟨i, B.mem_cutFinset_mk.mpr
      ⟨original, Or.inl ⟨hu, hv⟩⟩⟩)
  refine ⟨C, ?_⟩
  ext v
  rw [Set.mem_toFinset]
  constructor
  · intro hv
    have ha : a.val ∈ C.supp := (C.mem_supp_iff a.val).mpr rfl
    exact CycleRemoval.Internal.mem_of_reachable_of_cut_empty G closed
      (C.reachable_of_mem_supp ha hv) a.property
  · intro hv
    obtain ⟨p⟩ := inside.preconnected a ⟨v, hv⟩
    let hom : (G.induce {v | v ∈ P i}) →g G := ⟨Subtype.val, fun h => h⟩
    exact (C.mem_supp_iff v).mpr (SimpleGraph.ConnectedComponent.sound (p.map hom).reachable.symm)

theorem exists_region_embedding
    (connected : ∀ i, (B.induce {v | v ∈ P i}).Connected)
    (disjoint : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ∃ f : ι ↪ (B.deleteEdges (⋃ j, (B.cutFinset (P j) : Set (Sym2 V)))).ConnectedComponent,
      ∀ i, (f i).supp.toFinset = P i := by
  choose component support using exists_region_component B P connected disjoint
  refine ⟨⟨component, ?_⟩, support⟩
  intro i j equal
  by_contra different
  have hi : (component i).out ∈ P i := by
    rw [← support]
    exact Set.mem_toFinset.mpr (component i).out_eq
  have hj : (component i).out ∈ P j := by
    rw [equal, ← support]
    exact Set.mem_toFinset.mpr (component j).out_eq
  exact Finset.disjoint_left.mp (disjoint different) hi hj

theorem ncard_neighborSet_le_cut (F : Set (Sym2 V))
    (C : (B.deleteEdges F).ConnectedComponent) :
    ((graph B F).neighborSet C).ncard ≤ (B.cutFinset C.supp.toFinset).card := by
  let : Fintype (B.deleteEdges F).ConnectedComponent := Fintype.ofFinite _
  have chooseEdge (D : (graph B F).neighborSet C) :
      ∃ e ∈ B.cutFinset C.supp.toFinset,
        Sym2.map (B.deleteEdges F).connectedComponentMk e = s(C, D.val) := by
    obtain ⟨different, u, hu, v, hv, uv⟩ := D.property
    refine ⟨s(u, v), B.mem_cutFinset_mk.mpr ⟨uv, Or.inl ⟨Set.mem_toFinset.mpr hu, ?_⟩⟩, ?_⟩
    · intro hc
      exact different (SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (Set.mem_toFinset.mp hc) hv)
    · change s((B.deleteEdges F).connectedComponentMk u, (B.deleteEdges F).connectedComponentMk v) = _
      rw [(C.mem_supp_iff u).mp hu, (D.val.mem_supp_iff v).mp hv]
  choose edge member image using chooseEdge
  let f : (graph B F).neighborSet C → B.cutFinset C.supp.toFinset := fun D => ⟨edge D, member D⟩
  have injective : Function.Injective f := by
    intro D E equal
    have pair : s(C, D.val) = s(C, E.val) := (image D).symm.trans
      ((congrArg (fun e => Sym2.map (B.deleteEdges F).connectedComponentMk e)
        (congrArg Subtype.val equal)).trans (image E))
    apply Subtype.ext
    rcases Sym2.eq_iff.mp pair with ⟨_, h⟩ | ⟨h, h'⟩
    · exact h
    · exact h'.trans h
  have bound := Fintype.card_le_of_injective f injective
  rw [Set.fintypeCard_eq_ncard, Fintype.card_coe] at bound
  exact bound

theorem ncard_neighborSet_eq_cut (F : Set (Sym2 V))
    (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e)
    (C : (B.deleteEdges F).ConnectedComponent) :
    ((graph B F).neighborSet C).ncard = (B.cutFinset C.supp.toFinset).card := by
  let : Fintype (B.deleteEdges F).ConnectedComponent := Fintype.ofFinite _
  apply Nat.le_antisymm (ncard_neighborSet_le_cut B F C)
  have chooseNeighbor (e : B.cutFinset C.supp.toFinset) :
      e.val ∈ F ∩ B.edgeSet ∧ ∃ D : (graph B F).neighborSet C,
        Sym2.map (B.deleteEdges F).connectedComponentMk e.val = s(C, D.val) := by
    obtain ⟨edge, a, b, equal, ha, hb⟩ := B.mem_cutFinset.mp e.property
    have inside : a ∈ C.supp := Set.mem_toFinset.mp ha
    have outside : b ∉ C.supp := fun h => hb (Set.mem_toFinset.mpr h)
    let D := (B.deleteEdges F).connectedComponentMk b
    have inD : b ∈ D.supp := (D.mem_supp_iff b).mpr rfl
    have different : C ≠ D := fun h => outside (h ▸ inD)
    have deleted : e.val ∈ F := by
      by_contra fresh
      have kept : (B.deleteEdges F).Adj a b := SimpleGraph.deleteEdges_adj.mpr
        ⟨B.mem_edgeSet.mp (equal ▸ edge), by simpa only [← equal] using fresh⟩
      exact outside (C.mem_supp_of_adj_mem_supp inside kept)
    refine ⟨⟨deleted, edge⟩, ⟨D, different, a, inside, b, inD,
      B.mem_edgeSet.mp (equal ▸ edge)⟩, ?_⟩
    change Sym2.map (B.deleteEdges F).connectedComponentMk e.val = s(C, D)
    rw [equal]
    change s((B.deleteEdges F).connectedComponentMk a, D) = s(C, D)
    rw [(C.mem_supp_iff a).mp inside]
  choose member neighbor image using chooseNeighbor
  have injective : Function.Injective neighbor := by
    intro e f equal
    apply Subtype.ext
    apply edge_map_injOn B F bridges (member e) (member f)
    rw [image e, image f, equal]
  have bound := Fintype.card_le_of_injective neighbor injective
  rw [Fintype.card_coe, Set.fintypeCard_eq_ncard] at bound
  exact bound

end Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal
