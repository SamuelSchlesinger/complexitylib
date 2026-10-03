/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient

/-!
# Constructing the core forest from the region family

Disjoint connected regions with no edges between them give independent
vertices in their boundary quotient. Their cuts bound their quotient
degrees. If cycles avoid the regions and their cuts have size at most two,
suppressing these vertices gives a forest on the remaining core pieces,
with exact reachability inherited from the original graph.
Its edges count exactly the regions whose remaining boundary has size two.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression.Internal

open scoped Classical

variable {V ι : Type} [Fintype V] [Fintype ι] (B : SimpleGraph V) (P : ι → Finset V)

theorem exists_core_forest
    (connected : ∀ i, (B.induce {v | v ∈ P i}).Connected)
    (disjoint : Pairwise (fun i j => Disjoint (P i) (P j)))
    (separate : ∀ i j, ∀ u ∈ P i, ∀ v ∈ P j, B.Adj u v → i = j)
    (boundary : ∀ i, (B.cutFinset (P i)).card ≤ 2)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support) :
    ∃ f : ι ↪ (B.deleteEdges (⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))).ConnectedComponent,
      (∀ i, (f i).supp.toFinset = P i) ∧ (coreGraph B P f).IsAcyclic ∧
      (coreGraph B P f).edgeSet.ncard =
        (Finset.univ.filter (fun i => (B.cutFinset (P i)).card = 2)).card ∧
      ∀ u v, (coreGraph B P f).Reachable u v ↔ B.Reachable u.val.out v.val.out := by
  let : Fintype (B.deleteEdges (⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))).ConnectedComponent :=
    Fintype.ofFinite _
  obtain ⟨f, support⟩ := BridgeQuotient.exists_region_embedding B P connected disjoint
  let S := Finset.univ.image f
  let Q := BridgeQuotient.ofRegions B P
  have independent : ∀ C ∈ S, ∀ D ∈ S, ¬ Q.Adj C D := by
    intro C hc D hd adjacent
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨different, u, hu, v, hv, uv⟩ := adjacent
    have memU : u ∈ P i := by rw [← support]; exact Set.mem_toFinset.mpr hu
    have memV : v ∈ P j := by rw [← support]; exact Set.mem_toFinset.mpr hv
    exact different (congrArg f (separate i j u memU v memV uv))
  have coreIndependent : ∀ C ∉ S, ∀ D ∉ S, ¬ Q.Adj C D := by
    intro C hc D hd adjacent
    obtain ⟨different, u, hu, v, hv, uv⟩ := adjacent
    have removed : s(u, v) ∈ ⋃ i, (B.cutFinset (P i) : Set (Sym2 V)) := by
      by_contra fresh
      have kept := SimpleGraph.deleteEdges_adj.mpr ⟨uv, fresh⟩
      exact different (SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (C.mem_supp_of_adj_mem_supp hu kept) hv)
    obtain ⟨i, member⟩ := Set.mem_iUnion.mp removed
    rcases (B.mem_cutFinset_mk.mp member).2 with ⟨hi, _⟩ | ⟨hi, _⟩
    · have inRegion : u ∈ (f i).supp := by
        apply Set.mem_toFinset.mp
        rwa [support]
      have same := SimpleGraph.ConnectedComponent.eq_of_common_vertex inRegion hu
      exact hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, same⟩)
    · have inRegion : v ∈ (f i).supp := by
        apply Set.mem_toFinset.mp
        rwa [support]
      have same := SimpleGraph.ConnectedComponent.eq_of_common_vertex inRegion hv
      exact hd (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, same⟩)
  have bridges : ∀ e ∈ (⋃ i, (B.cutFinset (P i) : Set (Sym2 V))) ∩ B.edgeSet,
      B.IsBridge e := by
    intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he.1
    exact BridgeQuotient.isBridge_of_mem_region_cut B P avoids hi
  have exactDegree (i : ι) : Q.degree (f i) = (B.cutFinset (P i)).card := by
    rw [← Q.ncard_neighborSet]
    change ((BridgeQuotient.graph B _).neighborSet (f i)).ncard = _
    rw [BridgeQuotient.ncard_neighborSet_eq_cut B _ bridges, support]
  have degree : ∀ C ∈ S, Q.degree C ≤ 2 := by
    intro C hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    rw [exactDegree]
    exact boundary i
  have active : S.filter (fun C => Q.degree C = 2) =
      (Finset.univ.filter (fun i => (B.cutFinset (P i)).card = 2)).image f := by
    ext C
    constructor
    · intro member
      obtain ⟨inside, two⟩ := Finset.mem_filter.mp member
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp inside
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by rwa [exactDegree] at two⟩, rfl⟩
    · intro member
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp member
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
        by rw [exactDegree]; exact (Finset.mem_filter.mp hi).2⟩
  have forest := BridgeQuotient.ofRegions_isAcyclic B P avoids
  have count := edge_ncard_eq_degree_two Q S forest independent coreIndependent degree
  rw [active, Finset.card_image_of_injective _ f.injective] at count
  refine ⟨f, support, isAcyclic Q S forest degree, count, ?_⟩
  intro u v
  exact (reachable_iff Q S independent).trans
    (BridgeQuotient.reachable_iff B (⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))
      u.val.out_eq v.val.out_eq)

end Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression.Internal
