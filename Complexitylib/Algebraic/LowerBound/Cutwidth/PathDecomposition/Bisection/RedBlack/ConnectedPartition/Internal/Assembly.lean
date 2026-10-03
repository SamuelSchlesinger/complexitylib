/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.ConnectedPartition.Internal.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.ConnectedPartition.Internal.Regions

/-!
# Joining rooted component partitions

The completed pieces from disjoint components remain separate. Their
remainders join through a new root; either that union is another completed
piece or it is the new small remainder.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition

open scoped Classical

variable {V : Type} {B : SimpleGraph V} {S : Finset V} {root : V} {M : Nat}

theorem Partial.part_subset (Q : Partial B S root M) {P : Finset V} (member : P ∈ Q.parts) :
    P ⊆ S := by
  intro v hv
  rw [← Q.cover]
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨P, member, hv⟩)

theorem Partial.remainder_subset (Q : Partial B S root M) : Q.remainder ⊆ S := by
  intro v hv
  have member : v ∈ Q.parts.biUnion id ∪ Q.remainder := Finset.mem_union_right _ hv
  simpa only [Q.cover] using member

namespace Internal

theorem assemble {ι : Type} [Fintype ι] (B : SimpleGraph V) (S : Finset V)
    (root : V) (M : Nat) (positive : 0 < M) (region : ι → Finset V)
    (regions : Pairwise fun i j => Disjoint (region i) (region j))
    (cover : insert root (Finset.univ.biUnion region) = S)
    (excluded : ∀ i, root ∉ region i) (count : Fintype.card ι ≤ 3)
    (neighbor : ι → V) (adjacent : ∀ i, B.Adj root (neighbor i))
    (data : ∀ i, Partial B (region i) (neighbor i) M) :
    Nonempty (Partial B S root M) := by
  let pieces := Finset.univ.biUnion fun i => (data i).parts
  let joined := insert root (Finset.univ.biUnion fun i => (data i).remainder)
  have piece_property : ∀ P ∈ pieces,
      (B.induce {v | v ∈ P}).Connected ∧ M ≤ P.card ∧ P.card ≤ 3 * M := by
    intro P hp
    obtain ⟨i, _, member⟩ := Finset.mem_biUnion.mp hp
    exact (data i).pieces P member
  have pairwise : (pieces : Set (Finset V)).Pairwise Disjoint := by
    intro P hp Q hq different
    obtain ⟨i, _, memberP⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, _, memberQ⟩ := Finset.mem_biUnion.mp hq
    by_cases same : i = j
    · subst j
      exact (data i).disjoint memberP memberQ different
    · exact (regions same).mono ((data i).part_subset memberP) ((data j).part_subset memberQ)
  have separated : ∀ P ∈ pieces, Disjoint P joined := by
    intro P hp
    obtain ⟨i, _, memberP⟩ := Finset.mem_biUnion.mp hp
    apply Finset.disjoint_left.mpr
    intro v hv hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact excluded i ((data i).part_subset memberP hv)
    · obtain ⟨j, _, memberJ⟩ := Finset.mem_biUnion.mp hj
      by_cases same : i = j
      · subst j
        exact Finset.disjoint_left.mp ((data i).separate P memberP) hv memberJ
      · exact Finset.disjoint_left.mp (regions same) ((data i).part_subset memberP hv)
          ((data j).remainder_subset memberJ)
  have joined_connected : (B.induce {v | v ∈ joined}).Connected :=
    connected_insert_biUnion B root (fun i => (data i).remainder) neighbor adjacent
      (fun i => (data i).rooted) Finset.univ
  have joined_size : joined.card ≤ 3 * M := by
    have small (i : ι) : (data i).remainder.card ≤ M - 1 := by
      have := (data i).small
      lia
    have total := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => small i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at total
    have bound := Nat.mul_le_mul_right (M - 1) count
    have unionBound := Finset.card_biUnion_le
      (s := (Finset.univ : Finset ι)) (t := fun i => (data i).remainder)
    have insertBound := Finset.card_insert_le root
      (Finset.univ.biUnion fun i => (data i).remainder)
    dsimp only [joined]
    lia
  have joined_cover : pieces.biUnion id ∪ joined = S := by
    rw [← cover]
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hp | hj
      · obtain ⟨P, hp, hv⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨i, _, member⟩ := Finset.mem_biUnion.mp hp
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, (data i).part_subset member hv⟩)
      · rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Finset.mem_insert_self _ _
        · obtain ⟨i, _, member⟩ := Finset.mem_biUnion.mp hj
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ _, (data i).remainder_subset member⟩)
    · intro hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · obtain ⟨i, _, member⟩ := Finset.mem_biUnion.mp hv
        have localMember : v ∈ (data i).parts.biUnion id ∪ (data i).remainder := by
          simpa only [(data i).cover] using member
        rcases Finset.mem_union.mp localMember with hp | hr
        · obtain ⟨P, hp, hvP⟩ := Finset.mem_biUnion.mp hp
          exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
            ⟨P, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩, hvP⟩)
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ _, hr⟩))
  by_cases large : M ≤ joined.card
  · refine ⟨{
      parts := insert joined pieces
      remainder := ∅
      cover := ?_
      disjoint := ?_
      separate := by simp
      pieces := ?_
      small := by simpa using positive
      rooted := Or.inl rfl }⟩
    · simpa only [Finset.biUnion_insert, id_eq, Finset.union_empty, Finset.union_comm,
        Finset.empty_union] using
        joined_cover
    · intro P hp Q hq different
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · exact (different rfl).elim
        · exact (separated Q hq).symm
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · exact separated P hp
        · exact pairwise hp hq different
    · intro P hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨joined_connected, large, joined_size⟩
      · exact piece_property P hp
  · exact ⟨{
      parts := pieces
      remainder := joined
      cover := joined_cover
      disjoint := pairwise
      separate := separated
      pieces := piece_property
      small := Nat.lt_of_not_ge large
      rooted := Or.inr ⟨Finset.mem_insert_self _ _, joined_connected⟩ }⟩

end Internal
end Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition
