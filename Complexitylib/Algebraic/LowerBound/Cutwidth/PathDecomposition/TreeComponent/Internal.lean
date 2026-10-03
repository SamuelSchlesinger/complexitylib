/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith

/-!
# Tree components from an edge deficit

The endpoint induction for subcubic path decompositions removes a tree
component of the complement of the prescribed last bag. An edge deficit
forces such a component; the degree-sum argument locates the deficit.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem exists_small_tree_component_of_edge_deficit (M : Nat)
    (deficit : (M + 1) * H.edgeFinset.card < M * Fintype.card W) :
    ∃ C : H.ConnectedComponent, C.toSimpleGraph.IsTree ∧ Fintype.card C ≤ M := by
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  by_contra! h
  have hdegree (C : H.ConnectedComponent) (v : C) :
      C.toSimpleGraph.degree v = H.degree v := by
    exact H.degree_induce_of_neighborSet_subset (v := v)
      (fun w hw => C.mem_supp_of_adj_mem_supp v.property hw)
  have hcomponent (C : H.ConnectedComponent) :
      2 * M * Fintype.card C ≤ (M + 1) * ∑ v : C, H.degree v := by
    have connected := C.connected_toSimpleGraph
    have hle := connected.card_vert_le_card_edgeSet_add_one
    simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hle
    have bound : M * Fintype.card C ≤ (M + 1) * C.toSimpleGraph.edgeFinset.card := by
      by_cases tree : C.toSimpleGraph.IsTree
      · have large := h C tree
        have scaled := Nat.mul_le_mul_left (M + 1) hle
        nlinarith
      · have hne : Nat.card C.toSimpleGraph.edgeSet + 1 ≠ Nat.card C :=
          fun heq => tree (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨connected, heq⟩)
        simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at hne
        have hge : Fintype.card C ≤ C.toSimpleGraph.edgeFinset.card := by lia
        exact (Nat.mul_le_mul_left M hge).trans (Nat.mul_le_mul_right _ (by lia))
    have degreeSum : (∑ v : C, H.degree v) = 2 * C.toSimpleGraph.edgeFinset.card := by
      rw [← C.toSimpleGraph.sum_degrees_eq_twice_card_edges]
      exact Finset.sum_congr rfl fun v _ => (hdegree C v).symm
    rw [degreeSum]
    nlinarith
  have hsum := Finset.sum_le_sum fun C (_ : C ∈ (Finset.univ : Finset H.ConnectedComponent)) =>
    hcomponent C
  have hcount : (∑ C : H.ConnectedComponent, 2 * M * Fintype.card C) =
      2 * M * Fintype.card W := by
    calc (∑ C : H.ConnectedComponent, 2 * M * Fintype.card C)
        = ∑ C : H.ConnectedComponent, ∑ _v : C, 2 * M := by simp [Nat.mul_comm]
      _ = ∑ _v : W, 2 * M :=
        Fintype.sum_fiberwise H.connectedComponentMk (fun _ => 2 * M)
      _ = 2 * M * Fintype.card W := by simp [Nat.mul_comm]
  have hdegrees : (∑ C : H.ConnectedComponent, ∑ v : C, H.degree v) =
      ∑ v : W, H.degree v :=
    Fintype.sum_fiberwise H.connectedComponentMk (fun v : W => H.degree v)
  rw [hcount, ← Finset.mul_sum, hdegrees, H.sum_degrees_eq_twice_card_edges] at hsum
  nlinarith

theorem exists_tree_component_of_card_edgeFinset_lt
    (hcard : H.edgeFinset.card < Fintype.card W) :
    ∃ C : H.ConnectedComponent, C.toSimpleGraph.IsTree := by
  have deficit : (Fintype.card W + 1) * H.edgeFinset.card <
      Fintype.card W * Fintype.card W := by
    have scaled := Nat.mul_le_mul_left (Fintype.card W + 1) (Nat.succ_le_of_lt hcard)
    nlinarith
  obtain ⟨C, tree, _⟩ := exists_small_tree_component_of_edge_deficit H _ deficit
  exact ⟨C, tree⟩

private theorem sum_outside_neighbors (X : Finset W) :
    (∑ v ∈ X, ((H.neighborFinset v) \ X).card) =
      ∑ v ∈ Xᶜ, ((H.neighborFinset v) ∩ X).card := by
  have above (v : W) : Xᶜ.bipartiteAbove H.Adj v = (H.neighborFinset v) \ X := by
    ext w
    simp only [Finset.mem_bipartiteAbove, Finset.mem_compl, Finset.mem_sdiff,
      SimpleGraph.mem_neighborFinset]
    tauto
  have below (v : W) : X.bipartiteBelow H.Adj v = (H.neighborFinset v) ∩ X := by
    ext w
    simp only [Finset.mem_bipartiteBelow, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    rw [H.adj_comm]
    tauto
  simpa only [above, below] using
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := X) (t := Xᶜ) H.Adj

theorem complement_card_edges_lt (X : Finset W)
    (degree : ∀ v, H.degree v ≤ 3) (large : Fintype.card W < 3 * X.card)
    (outside : ∀ v ∈ X, 2 ≤ ((H.neighborFinset v) \ X).card) :
    (H.induce {w | w ∉ X}).edgeFinset.card < Fintype.card {w : W // w ∉ X} := by
  let G := H.induce {w | w ∉ X}
  have localBound (v : {w : W // w ∉ X}) :
      G.degree v + ((H.neighborFinset v) ∩ X).card ≤ 3 := by
    have hmap := H.map_neighborFinset_induce (s := {w | w ∉ X}) v
    have heq : H.neighborFinset v ∩ ({w | w ∉ X} : Set W).toFinset =
        H.neighborFinset v \ X := by
      ext w
      simp
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map, heq] at hcard
    change G.degree v = (H.neighborFinset v \ X).card at hcard
    rw [hcard, Finset.card_sdiff_add_card_inter]
    exact degree v
  have total := Finset.sum_le_sum
    (fun v (_ : v ∈ (Finset.univ : Finset {w : W // w ∉ X})) => localBound v)
  have cross : (∑ v : {w : W // w ∉ X}, ((H.neighborFinset v) ∩ X).card) =
      ∑ v ∈ Xᶜ, ((H.neighborFinset v) ∩ X).card :=
    (Finset.sum_subtype Xᶜ (by simp) (fun v => ((H.neighborFinset v) ∩ X).card)).symm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    cross] at total
  have degreeSum : (∑ v : {w : W // w ∉ X}, G.degree v) = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have lower := Finset.sum_le_sum outside
  simp only [Finset.sum_const, nsmul_eq_mul, sum_outside_neighbors] at lower
  have cardinality : Fintype.card {w : W // w ∉ X} + X.card = Fintype.card W := by
    have hc := Finset.card_compl_add_card X
    convert hc using 1
    congr 1
    exact (Fintype.card_subtype_compl (fun w => w ∈ X)).trans
      (by simp [Finset.card_compl])
  change G.edgeFinset.card < Fintype.card {w : W // w ∉ X}
  lia

end Algebraic.Cutwidth.PathDecomposition.Internal
