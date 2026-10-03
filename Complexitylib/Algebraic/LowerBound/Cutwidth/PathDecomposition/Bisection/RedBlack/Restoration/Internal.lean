/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Finset.SymmDiff
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal

/-!
# Accounting for restored black edges

Isolating a set deletes its black cut. To transfer a positive set back to
the original graph, add the isolated set and pay for its remaining external
black edges with newly internal red edges. An overlap with the old witness
is allowed when that overlap has empty black cut.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.Internal

open scoped Classical symmDiff

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

theorem cut_deleteEdges (F : Finset (Sym2 V)) (X : Finset V) :
    (B.deleteEdges (F : Set (Sym2 V))).cutFinset X = B.cutFinset X \ F := by
  ext e
  obtain ⟨u, v⟩ := e
  simp only [SimpleGraph.mem_cutFinset_mk, SimpleGraph.deleteEdges_adj,
    Finset.mem_coe, Finset.mem_sdiff]
  tauto

theorem cut_union_of_closed_inter {X A : Finset V} (closed : B.cutFinset (X ∩ A) = ∅) :
    B.cutFinset (X ∪ A) = B.cutFinset X ∆ B.cutFinset A := by
  ext e
  obtain ⟨u, v⟩ := e
  have absent : s(u, v) ∉ B.cutFinset (X ∩ A) := by rw [closed]; simp
  simp only [SimpleGraph.mem_cutFinset_mk, Finset.mem_union, Finset.mem_inter,
    Finset.mem_symmDiff] at absent ⊢
  tauto

omit [Fintype V] in
theorem card_internalEdges_union_ge (X A : Finset V) :
    (internalEdges R X).card + (internalEdges R A \ internalEdges R X).card ≤
      (internalEdges R (X ∪ A)).card := by
  have disjoint : Disjoint (internalEdges R X) (internalEdges R A \ internalEdges R X) :=
    Finset.disjoint_left.mpr (fun _ hx ha => (Finset.mem_sdiff.mp ha).2 hx)
  rw [← Finset.card_union_of_disjoint disjoint]
  apply Finset.card_le_card
  intro e he
  obtain hx | ha := Finset.mem_union.mp he
  · exact internalEdges_mono R Finset.subset_union_left hx
  · exact internalEdges_mono R Finset.subset_union_right (Finset.mem_sdiff.mp ha).1

theorem positive_restore_cut {X A : Finset V}
    (positive : Positive (B.deleteEdges (B.cutFinset A : Set (Sym2 V))) R X)
    (closed : B.cutFinset (X ∩ A) = ∅)
    (budget : (B.cutFinset A \ B.cutFinset X).card ≤
      (internalEdges R A \ internalEdges R X).card) : Positive B R (X ∪ A) := by
  change ((B.deleteEdges (B.cutFinset A : Set (Sym2 V))).cutFinset X).card <
    (internalEdges R X).card at positive
  rw [cut_deleteEdges] at positive
  change (B.cutFinset (X ∪ A)).card < (internalEdges R (X ∪ A)).card
  rw [cut_union_of_closed_inter B closed, Finset.symmDiff_def,
    Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  have red := card_internalEdges_union_ge R X A
  lia

theorem positive_restore_two_boundary {X A : Finset V}
    (positive : Positive (B.deleteEdges (B.cutFinset A : Set (Sym2 V))) R X)
    (closed : B.cutFinset (X ∩ A) = ∅)
    (two : (B.cutFinset A).card ≤ 2)
    (crossing : (B.cutFinset A ∩ B.cutFinset X).Nonempty)
    (newRed : (internalEdges R A \ internalEdges R X).Nonempty) :
    Positive B R (X ∪ A) := by
  apply positive_restore_cut B R positive closed
  have count := Finset.card_sdiff_add_card_inter (B.cutFinset A) (B.cutFinset X)
  have common := Finset.card_pos.mpr crossing
  have red := Finset.card_pos.mpr newRed
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.Internal
