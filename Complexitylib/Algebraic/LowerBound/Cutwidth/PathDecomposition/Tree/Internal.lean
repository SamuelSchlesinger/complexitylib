/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Nat.Log
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Components
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations

/-!
# Tree separators and path decompositions

A vertex minimizing the sum of distances is a centroid: every component
left after deleting it contains at most half the vertices. This supplies
the balanced recursion used for logarithmic-width tree decompositions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} {H : SimpleGraph W}

private theorem path_length_eq_dist (tree : H.IsTree) {u v : W}
    (p : H.Walk u v) (hp : p.IsPath) : p.length = H.dist u v := by
  obtain ⟨q, hq, hlength⟩ := tree.connected.exists_path_of_dist u v
  have heq := (tree.isAcyclic.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  exact (congrArg (fun t : H.Path u v => t.val.length) heq).trans hlength

private theorem neighbor_of_walk (r : W)
    (C : (H.induce {w | w ≠ r}).ConnectedComponent) {w : W}
    (hw : w ≠ r) (hC : (⟨w, hw⟩ : {w : W // w ≠ r}) ∈ C.supp)
    (p : H.Walk w r) :
    ∃ a : {w : W // w ≠ r}, a ∈ C.supp ∧ H.Adj r a := by
  cases p with
  | nil => exact (hw rfl).elim
  | @cons w u r hadj p =>
    by_cases hu : u = r
    · subst u
      exact ⟨⟨w, hw⟩, hC, hadj.symm⟩
    · exact neighbor_of_walk r C hu (C.mem_supp_of_adj_mem_supp hC hadj) p

private theorem component_has_root_neighbor (connected : H.Connected) (r : W)
    (C : (H.induce {w | w ≠ r}).ConnectedComponent) :
    ∃ a : {w : W // w ≠ r}, a ∈ C.supp ∧ H.Adj r a := by
  obtain ⟨w, hw⟩ := C.nonempty_supp
  exact neighbor_of_walk r C w.property hw (connected w r).some

private theorem component_dist (tree : H.IsTree) (r : W)
    (C : (H.induce {w | w ≠ r}).ConnectedComponent)
    {a w : {w : W // w ≠ r}} (ha : a ∈ C.supp) (hw : w ∈ C.supp)
    (hadj : H.Adj r a) : H.dist r w = H.dist a w + 1 := by
  obtain ⟨p, hp, _⟩ := (C.reachable_of_mem_supp ha hw).exists_path_of_dist
  let f := (SimpleGraph.Embedding.induce {w | w ≠ r} (G := H)).toHom
  have hmap : (p.map f).IsPath := hp.map Subtype.val_injective
  have hr : r ∉ (p.map f).support := by
    rw [SimpleGraph.Walk.support_map]
    rintro h
    obtain ⟨v, _, hv⟩ := List.mem_map.mp h
    exact v.property hv
  have hroot := path_length_eq_dist tree (.cons hadj (p.map f)) (hmap.cons hr)
  have hdist := path_length_eq_dist tree (p.map f) hmap
  change (p.map f).length + 1 = H.dist r w at hroot
  change (p.map f).length = H.dist a w at hdist
  lia

theorem exists_tree_centroid [Fintype W] (tree : H.IsTree) :
    ∃ r : W, ∀ C : (H.induce {w | w ≠ r}).ConnectedComponent,
      2 * Fintype.card C ≤ Fintype.card W := by
  have : Nonempty W := tree.connected.nonempty
  let potential (r : W) := ∑ w : W, H.dist r w
  obtain ⟨r, _, minimal⟩ := Finset.exists_min_image Finset.univ potential Finset.univ_nonempty
  refine ⟨r, fun C => ?_⟩
  obtain ⟨a, ha, hadj⟩ := component_has_root_neighbor tree.connected r C
  let S : Finset W := C.supp.toFinset.map (.subtype (· ≠ r))
  have memS (w : W) : w ∈ S ↔ ∃ hw : w ≠ r, (⟨w, hw⟩ : {w : W // w ≠ r}) ∈ C.supp := by
    simp only [S, Finset.mem_map, Set.mem_toFinset, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨⟨w', hw'⟩, hC, rfl⟩
      exact ⟨hw', hC⟩
    · rintro ⟨hw, hC⟩
      exact ⟨⟨w, hw⟩, hC, rfl⟩
  have inside : (∑ w ∈ S, H.dist a w) + S.card = ∑ w ∈ S, H.dist r w := by
    calc (∑ w ∈ S, H.dist a w) + S.card = ∑ w ∈ S, (H.dist a w + 1) := by
          simp [Finset.sum_add_distrib]
      _ = ∑ w ∈ S, H.dist r w := by
        apply Finset.sum_congr rfl
        intro w hw
        obtain ⟨hne, hC⟩ := (memS w).mp hw
        exact (component_dist tree r C ha hC hadj).symm
  have outside : (∑ w ∈ Sᶜ, H.dist a w) ≤ (∑ w ∈ Sᶜ, H.dist r w) + Sᶜ.card := by
    calc (∑ w ∈ Sᶜ, H.dist a w) ≤ ∑ w ∈ Sᶜ, (H.dist r w + 1) := by
          apply Finset.sum_le_sum
          intro w _
          have h := tree.connected.dist_triangle (u := (a : W)) (v := r) (w := w)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at h
          lia
      _ = (∑ w ∈ Sᶜ, H.dist r w) + Sᶜ.card := by simp [Finset.sum_add_distrib]
  have atA := Finset.sum_add_sum_compl S (fun w => H.dist a w)
  have atR := Finset.sum_add_sum_compl S (fun w => H.dist r w)
  have minA : potential r ≤ potential a := minimal a (Finset.mem_univ _)
  have cardS : S.card = Fintype.card C := by
    rw [Finset.card_map]
    exact Set.toFinset_card C.supp
  have total := Finset.card_compl_add_card S
  dsimp [potential] at minA
  lia

theorem exists_tree_decomposition_of_card_le_pow (k : Nat) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W), H.IsTree → Fintype.card W ≤ 2 ^ k →
      ∃ D : PathDecomposition H, ∀ i, (D.bag i).card ≤ k + 1 := by
  induction k with
  | zero =>
    intro W _ H _ hcard
    refine ⟨.trivial H, fun _ => ?_⟩
    simpa only [trivial, Finset.card_univ, Nat.pow_zero] using hcard
  | succ k ih =>
    intro W _ H tree hcard
    obtain ⟨r, centroid⟩ := exists_tree_centroid tree
    have parts (C : (H.induce {w | w ≠ r}).ConnectedComponent) :
        ∃ D : PathDecomposition C.toSimpleGraph, ∀ i, (D.bag i).card ≤ k + 1 := by
      have acyclic : C.toSimpleGraph.IsAcyclic :=
        (tree.isAcyclic.induce {w | w ≠ r}).induce C.supp
      apply ih C C.toSimpleGraph ⟨C.connected_toSimpleGraph, acyclic⟩
      have hhalf := centroid C
      rw [Nat.pow_succ] at hcard
      lia
    obtain ⟨D, bound⟩ := exists_of_components parts
    obtain ⟨D', _, bound'⟩ := exists_addVertex r D bound
    exact ⟨D', bound'⟩

theorem exists_tree_decomposition [Fintype W] (tree : H.IsTree) :
    ∃ D : PathDecomposition H,
      ∀ i, (D.bag i).card ≤ Nat.clog 2 (Fintype.card W) + 1 :=
  exists_tree_decomposition_of_card_le_pow _ W H tree (Nat.le_pow_clog (by lia) _)

theorem exists_forest_decomposition [Fintype W] (forest : H.IsAcyclic) :
    ∃ D : PathDecomposition H,
      ∀ i, (D.bag i).card ≤ Nat.clog 2 (Fintype.card W) + 1 := by
  apply exists_of_components
  intro C
  have tree : C.toSimpleGraph.IsTree := ⟨C.connected_toSimpleGraph, forest.induce C.supp⟩
  apply exists_tree_decomposition_of_card_le_pow _ C C.toSimpleGraph tree
  exact (Fintype.card_subtype_le _).trans (Nat.le_pow_clog (by lia) _)

end Algebraic.Cutwidth.PathDecomposition.Internal
