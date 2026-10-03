/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.ConnectedPartition.Internal.Assembly

/-!
# Bounded connected partitions of subcubic graphs

Induction on the vertex set partitions each connected region into pieces
of size between `M` and `3 M`, with at most one smaller rooted remainder.
There are at most three components after removing a root, so joining their
remainders stays within the size bound. Adding the final remainder gives
at most `2 n / M` pieces whenever `n > M`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition.Internal

open scoped Classical
open PathSystem PathSystem.Internal

variable {V : Type} [Fintype V] (B : SimpleGraph V)

theorem exists_partial (degree : ∀ v, B.degree v ≤ 3) (M : Nat) (positive : 0 < M)
    (S : Finset V) (root : V) (member : root ∈ S)
    (connected : (B.induce {v | v ∈ S}).Connected) : Nonempty (Partial B S root M) := by
  suffices ∀ n : Nat, ∀ (S : Finset V) (root : V), S.card = n → root ∈ S →
      (B.induce {v | v ∈ S}).Connected → Nonempty (Partial B S root M) by
    exact this S.card S root rfl member connected
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S root size member connected
    let U := S.erase root
    let ι := (B.induce {v | v ∈ U}).ConnectedComponent
    let : Fintype ι := Fintype.ofFinite _
    choose neighbor inside adjacent using exists_root_neighbor B member connected
    have recur (C : ι) : Nonempty (Partial B (region B U C) (neighbor C) M) := by
      apply ih (region B U C).card
      · have upper := Finset.card_le_card (region_subset B U C)
        have erase := Finset.card_erase_lt_of_mem member
        dsimp only [U] at upper
        lia
      · exact rfl
      · exact inside C
      · exact region_connected B U C
    let data (C : ι) := Classical.choice (recur C)
    have cover : insert root (Finset.univ.biUnion (region B U)) = S := by
      have union : Finset.univ.biUnion (region B U) = U := by
        ext v
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact exists_mem_region B U
      rw [union]
      exact Finset.insert_erase member
    have count : Fintype.card ι ≤ 3 := by
      have bound := (card_components_erase_le_degree B member connected).trans (degree root)
      simpa only [Nat.card_eq_fintype_card] using bound
    exact assemble B S root M positive (region B U) (region_disjoint B U) cover
      (fun C h => (Finset.mem_erase.mp (region_subset B U C h)).1 rfl) count
      neighbor adjacent data

theorem exists_partition (connected : B.Connected) (degree : ∀ v, B.degree v ≤ 3)
    (M : Nat) (positive : 0 < M) (large : M < Fintype.card V) :
    ∃ parts : Finset (Finset V), parts.biUnion id = Finset.univ ∧
      (parts : Set (Finset V)).Pairwise Disjoint ∧
      (∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected ∧ P.card ≤ 3 * M) ∧
      M * parts.card ≤ 2 * Fintype.card V := by
  let root : V := Classical.choice connected.nonempty
  have induced : (B.induce {v | v ∈ (Finset.univ : Finset V)}).Connected := by
    have same : {v | v ∈ (Finset.univ : Finset V)} = Set.univ := by ext; simp
    rw [same]
    exact (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso B)).mpr connected
  obtain ⟨Q⟩ := exists_partial B degree M positive Finset.univ root (Finset.mem_univ _) induced
  have count : M * Q.parts.card ≤ Fintype.card V := by
    have lower := Finset.sum_le_sum (fun P (hp : P ∈ Q.parts) => (Q.pieces P hp).2.1)
    simp only [Finset.sum_const, nsmul_eq_mul] at lower
    have union := Finset.card_biUnion (s := Q.parts) (t := id) Q.disjoint
    have upper := Finset.card_le_card
      (Finset.subset_univ (Q.parts.biUnion id))
    rw [union] at upper
    simp only [id_eq, Finset.card_univ] at upper
    lia
  by_cases empty : Q.remainder = ∅
  · refine ⟨Q.parts, ?_, Q.disjoint, ?_, by lia⟩
    · simpa only [empty, Finset.union_empty] using Q.cover
    · intro P hp
      exact ⟨(Q.pieces P hp).1, (Q.pieces P hp).2.2⟩
  · have remainder := Q.rooted.resolve_left empty
    refine ⟨insert Q.remainder Q.parts, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.biUnion_insert, id_eq, Finset.union_comm] using Q.cover
    · intro P hp T ht different
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases Finset.mem_insert.mp ht with rfl | ht
        · exact (different rfl).elim
        · exact (Q.separate T ht).symm
      · rcases Finset.mem_insert.mp ht with rfl | ht
        · exact Q.separate P hp
        · exact Q.disjoint hp ht different
    · intro P hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨remainder.2, by have := Q.small; lia⟩
      · exact ⟨(Q.pieces P hp).1, (Q.pieces P hp).2.2⟩
    · have upper := Nat.mul_le_mul_left M (Finset.card_insert_le Q.remainder Q.parts)
      lia

end Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition.Internal
