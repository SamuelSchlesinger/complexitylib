/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Connectivity and acyclicity of bridge quotients

Walks project to the component quotient and quotient walks lift through
the connected contracted pieces. An original bridge remains a bridge in
the quotient: a quotient path avoiding its image would lift to an original
path avoiding the bridge. Thus contracting along the complement of a set
of bridges produces a forest, and a tree when the original graph is connected.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal

variable {V : Type} (B : SimpleGraph V) (F : Set (Sym2 V))

private theorem lift_reachable (K : SimpleGraph V)
    (Q : SimpleGraph (B.deleteEdges F).ConnectedComponent) (kept : B.deleteEdges F ≤ K)
    (adjacent : ∀ C D, Q.Adj C D → ∃ u ∈ C.supp, ∃ v ∈ D.supp, K.Adj u v)
    {C D : (B.deleteEdges F).ConnectedComponent} (reachable : Q.Reachable C D)
    {u v : V} (hu : u ∈ C.supp) (hv : v ∈ D.supp) : K.Reachable u v := by
  obtain ⟨p⟩ := reachable
  induction p generalizing u v with
  | @nil C => exact (C.reachable_of_mem_supp hu hv).mono kept
  | @cons C D E edge p ih =>
    obtain ⟨a, ha, b, hb, ab⟩ := adjacent C D edge
    exact ((C.reachable_of_mem_supp hu ha).mono kept).trans (ab.reachable.trans (ih hb hv))

theorem reachable_lift {C D : (B.deleteEdges F).ConnectedComponent}
    (reachable : (graph B F).Reachable C D) {u v : V} (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    B.Reachable u v :=
  lift_reachable B F B (graph B F) (SimpleGraph.deleteEdges_le _) (fun _ _ h => h.2)
    reachable hu hv

theorem reachable_project {u v : V} (reachable : B.Reachable u v) :
    (graph B F).Reachable ((B.deleteEdges F).connectedComponentMk u)
      ((B.deleteEdges F).connectedComponentMk v) := by
  obtain ⟨p⟩ := reachable
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons a b c ab p ih =>
    by_cases same : (B.deleteEdges F).connectedComponentMk a =
        (B.deleteEdges F).connectedComponentMk b
    · exact same ▸ ih
    · have edge : (graph B F).Adj ((B.deleteEdges F).connectedComponentMk a)
          ((B.deleteEdges F).connectedComponentMk b) := by
        refine ⟨same, a, ?_, b, ?_, ab⟩ <;> exact
          (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
      exact edge.reachable.trans ih

theorem reachable_iff {C D : (B.deleteEdges F).ConnectedComponent} {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    (graph B F).Reachable C D ↔ B.Reachable u v := by
  refine ⟨fun h => reachable_lift B F h hu hv, fun h => ?_⟩
  have projected := reachable_project B F h
  rwa [(C.mem_supp_iff u).mp hu, (D.mem_supp_iff v).mp hv] at projected

theorem connected (original : B.Connected) : (graph B F).Connected where
  preconnected C D := (reachable_iff B F C.out_eq D.out_eq).mpr
    (original.preconnected C.out D.out)
  nonempty := original.nonempty.map (B.deleteEdges F).connectedComponentMk

private theorem edge_mem_deleted {C D : (B.deleteEdges F).ConnectedComponent}
    (different : C ≠ D) {u v : V} (hu : u ∈ C.supp) (hv : v ∈ D.supp)
    (adjacent : B.Adj u v) : s(u, v) ∈ F := by
  by_contra fresh
  have kept : (B.deleteEdges F).Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨adjacent, fresh⟩
  exact different (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (C.mem_supp_of_adj_mem_supp hu kept) hv)

private theorem endpoints_ne_of_bridge {u v : V} (bridge : B.IsBridge s(u, v))
    (removed : s(u, v) ∈ F) :
    (B.deleteEdges F).connectedComponentMk u ≠ (B.deleteEdges F).connectedComponentMk v := by
  intro equal
  exact (SimpleGraph.isBridge_iff.mp bridge)
    ((SimpleGraph.ConnectedComponent.exact equal).mono
      (SimpleGraph.deleteEdges_anti (Set.singleton_subset_iff.mpr removed)))

theorem edge_image (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Sym2.map (B.deleteEdges F).connectedComponentMk '' (F ∩ B.edgeSet) =
      (graph B F).edgeSet := by
  ext e
  constructor
  · rintro ⟨e, member, rfl⟩
    obtain ⟨u, v⟩ := e
    apply (graph B F).mem_edgeSet.mpr
    refine ⟨endpoints_ne_of_bridge B F (bridges _ member) member.1, u, ?_, v, ?_,
      B.mem_edgeSet.mp member.2⟩ <;> exact
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  · intro member
    obtain ⟨C, D⟩ := e
    obtain ⟨different, u, hu, v, hv, uv⟩ := (graph B F).mem_edgeSet.mp member
    refine ⟨s(u, v), ⟨edge_mem_deleted B F different hu hv uv, B.mem_edgeSet.mpr uv⟩, ?_⟩
    change s((B.deleteEdges F).connectedComponentMk u, (B.deleteEdges F).connectedComponentMk v) = _
    rw [(C.mem_supp_iff u).mp hu, (D.mem_supp_iff v).mp hv]

theorem edge_map_injOn (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    Set.InjOn (Sym2.map (B.deleteEdges F).connectedComponentMk) (F ∩ B.edgeSet) := by
  intro e he f hf equal
  obtain ⟨u, v⟩ := e
  obtain ⟨a, b⟩ := f
  by_contra different
  have kept : B.deleteEdges F ≤ B.deleteEdges {s(u, v)} :=
    SimpleGraph.deleteEdges_anti (Set.singleton_subset_iff.mpr he.1)
  have adjacent : (B.deleteEdges {s(u, v)}).Adj a b := by
    refine SimpleGraph.deleteEdges_adj.mpr ⟨B.mem_edgeSet.mp hf.2, ?_⟩
    exact fun h => different (Set.mem_singleton_iff.mp h).symm
  apply SimpleGraph.isBridge_iff.mp (bridges _ he)
  change s((B.deleteEdges F).connectedComponentMk u, (B.deleteEdges F).connectedComponentMk v) =
    s((B.deleteEdges F).connectedComponentMk a, (B.deleteEdges F).connectedComponentMk b) at equal
  rcases Sym2.eq_iff.mp equal with ⟨left, right⟩ | ⟨left, right⟩
  · exact ((SimpleGraph.ConnectedComponent.exact left).mono kept).trans
      (adjacent.reachable.trans ((SimpleGraph.ConnectedComponent.exact right.symm).mono kept))
  · exact ((SimpleGraph.ConnectedComponent.exact left).mono kept).trans
      (adjacent.symm.reachable.trans ((SimpleGraph.ConnectedComponent.exact right.symm).mono kept))

theorem edge_ncard (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).edgeSet.ncard = (F ∩ B.edgeSet).ncard := by
  rw [← edge_image B F bridges]
  exact (edge_map_injOn B F bridges).ncard_image

theorem isBridge_of_adj (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e)
    {C D : (B.deleteEdges F).ConnectedComponent} (edge : (graph B F).Adj C D) :
    (graph B F).IsBridge s(C, D) := by
  obtain ⟨different, u, hu, v, hv, uv⟩ := edge
  have removed := edge_mem_deleted B F different hu hv uv
  have bridge := bridges _ ⟨removed, B.mem_edgeSet.mpr uv⟩
  apply SimpleGraph.isBridge_iff.mpr
  intro reachable
  have kept : B.deleteEdges F ≤ B.deleteEdges {s(u, v)} :=
    SimpleGraph.deleteEdges_anti (Set.singleton_subset_iff.mpr removed)
  have allowed (A D' : (B.deleteEdges F).ConnectedComponent)
      (adjacent : ((graph B F).deleteEdges {s(C, D)}).Adj A D') :
      ∃ a ∈ A.supp, ∃ b ∈ D'.supp, (B.deleteEdges {s(u, v)}).Adj a b := by
    obtain ⟨⟨_, a, ha, b, hb, ab⟩, fresh⟩ := SimpleGraph.deleteEdges_adj.mp adjacent
    refine ⟨a, ha, b, hb, SimpleGraph.deleteEdges_adj.mpr ⟨ab, ?_⟩⟩
    intro equal
    have pair : s(a, b) = s(u, v) := Set.mem_singleton_iff.mp equal
    rcases Sym2.eq_iff.mp pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have left := SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hu
      have right := SimpleGraph.ConnectedComponent.eq_of_common_vertex hb hv
      exact fresh (by simp [left, right])
    · have left := SimpleGraph.ConnectedComponent.eq_of_common_vertex ha hv
      have right := SimpleGraph.ConnectedComponent.eq_of_common_vertex hb hu
      exact fresh (by simp [left, right, Sym2.eq_swap])
  exact (SimpleGraph.isBridge_iff.mp bridge)
    (lift_reachable B F _ _ kept allowed reachable hu hv)

theorem isAcyclic (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) : (graph B F).IsAcyclic :=
  SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
    (fun _ _ edge => isBridge_of_adj B F bridges edge)

theorem isTree (original : B.Connected) (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e) :
    (graph B F).IsTree :=
  ⟨connected B F original, isAcyclic B F bridges⟩

theorem component_isTree (bridges : ∀ e ∈ F ∩ B.edgeSet, B.IsBridge e)
    (C : (graph B F).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  ⟨C.connected_toSimpleGraph, (isAcyclic B F bridges).induce C.supp⟩

variable [Fintype V]

theorem isBridge_of_mem_region_cut {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    {i : ι} {e : Sym2 V} (member : e ∈ B.cutFinset (P i)) : B.IsBridge e := by
  obtain ⟨edge, a, b, rfl, ha, _⟩ := B.mem_cutFinset.mp member
  apply (SimpleGraph.isBridge_iff_forall_cycle_notMem edge).mpr
  intro u p cycle member
  exact avoids u p cycle i a ha (p.fst_mem_support_of_mem_edges member)

theorem ofRegions_isAcyclic {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support) :
    (ofRegions B P).IsAcyclic := by
  apply isAcyclic
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he.1
  exact isBridge_of_mem_region_cut B P avoids hi

theorem ofRegions_component_isTree {ι : Type} (P : ι → Finset V)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support)
    (C : (ofRegions B P).ConnectedComponent) : C.toSimpleGraph.IsTree :=
  ⟨C.connected_toSimpleGraph, (ofRegions_isAcyclic B P avoids).induce C.supp⟩

end Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient.Internal
