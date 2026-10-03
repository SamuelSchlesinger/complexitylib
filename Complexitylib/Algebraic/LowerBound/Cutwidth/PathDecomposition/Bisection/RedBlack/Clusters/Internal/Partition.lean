/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.ConnectedPartition.Internal

/-!
# Partitioning the large black components

Lift connected partitions of individual black components to the original
vertex type and combine them. Distinct components have disjoint supports,
so the resulting pieces partition the complement of the small components.
Summing the componentwise bounds controls the total number of pieces.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

private theorem lift_component_partition (M : ℕ) (C : B.ConnectedComponent)
    (parts : Finset (Finset C)) (cover : parts.biUnion id = Finset.univ)
    (disjoint : (parts : Set (Finset C)).Pairwise Disjoint)
    (pieces : ∀ P ∈ parts, (C.toSimpleGraph.induce {v | v ∈ P}).Connected ∧ P.card ≤ 3 * M)
    (count : M * parts.card ≤ 2 * Fintype.card C) :
    ∃ lifted : Finset (Finset V), lifted.biUnion id = C.supp.toFinset ∧
      (lifted : Set (Finset V)).Pairwise Disjoint ∧
      (∀ P ∈ lifted, (B.induce {v | v ∈ P}).Connected ∧ P.card ≤ 3 * M) ∧
      M * lifted.card ≤ 2 * Fintype.card C := by
  let embedding : C ↪ V := Function.Embedding.subtype _
  let lift : Finset C → Finset V := fun P => P.map embedding
  refine ⟨parts.image lift, ?_, ?_, ?_, ?_⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨P, hP, inside⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨w, _, same⟩ := Finset.mem_map.mp inside
      exact Set.mem_toFinset.mpr (same ▸ w.property)
    · intro hv
      let w : C := ⟨v, Set.mem_toFinset.mp hv⟩
      have member : w ∈ parts.biUnion id := by rw [cover]; exact Finset.mem_univ _
      obtain ⟨P, hP, inside⟩ := Finset.mem_biUnion.mp member
      exact Finset.mem_biUnion.mpr ⟨lift P, Finset.mem_image.mpr ⟨P, hP, rfl⟩,
        Finset.mem_map.mpr ⟨w, inside, rfl⟩⟩
  · intro P hP Q hQ different
    obtain ⟨p, memberP, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨q, memberQ, rfl⟩ := Finset.mem_image.mp hQ
    exact (Finset.disjoint_map embedding).mpr
      (disjoint memberP memberQ (fun same => different (congrArg lift same)))
  · intro P hP
    obtain ⟨p, memberP, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨?_, by simpa only [lift, Finset.card_map] using (pieces p memberP).2⟩
    let hom : (C.toSimpleGraph.induce {v | v ∈ p}) →g B.induce {v | v ∈ lift p} :=
      ⟨fun v => ⟨v.val.val, Finset.mem_map.mpr ⟨v.val, v.property, rfl⟩⟩, fun h => h⟩
    apply (pieces p memberP).1.map hom
    intro v
    obtain ⟨w, hw, same⟩ := Finset.mem_map.mp v.property
    exact ⟨⟨w, hw⟩, Subtype.ext same⟩
  · have sameCard : (parts.image lift).card = parts.card :=
      Finset.card_image_of_injective _ (Finset.map_injective embedding)
    rw [sameCard]
    exact count

private theorem assemble_component_partitions (M : ℕ) (U : Finset V)
    (small_iff : ∀ v, v ∈ U ↔ Fintype.card (B.connectedComponentMk v) ≤ M)
    (componentParts : ∀ C : B.ConnectedComponent, M < Fintype.card C →
      ∃ parts : Finset (Finset V), parts.biUnion id = C.supp.toFinset ∧
        (parts : Set (Finset V)).Pairwise Disjoint ∧
        (∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected ∧ P.card ≤ 3 * M) ∧
        M * parts.card ≤ 2 * Fintype.card C) :
    ∃ parts : Finset (Finset V), parts.biUnion id = Finset.univ \ U ∧
      (parts : Set (Finset V)).Pairwise Disjoint ∧
      (∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected ∧ P.card ≤ 3 * M) ∧
      M * parts.card ≤ 2 * (Finset.univ \ U).card := by
  let Large := {C : B.ConnectedComponent // M < Fintype.card C}
  let : Fintype Large := Fintype.ofFinite _
  choose parts cover disjoint pieces count using
    fun C : Large => componentParts C.val C.property
  let allParts := Finset.univ.biUnion parts
  have regionCover :
      Finset.univ.biUnion (fun C : Large => C.val.supp.toFinset) = Finset.univ \ U := by
    ext v
    constructor
    · intro hv
      obtain ⟨C, _, inside⟩ := Finset.mem_biUnion.mp hv
      have same := (C.val.mem_supp_iff v).mp (Set.mem_toFinset.mp inside)
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro small
      have bound := (small_iff v).mp small
      rw [same] at bound
      exact (Nat.not_le_of_lt C.property) bound
    · intro hv
      have large : M < Fintype.card (B.connectedComponentMk v) := by
        apply Nat.lt_of_not_ge
        intro bound
        exact (Finset.mem_sdiff.mp hv).2 ((small_iff v).mpr bound)
      exact Finset.mem_biUnion.mpr ⟨⟨B.connectedComponentMk v, large⟩, Finset.mem_univ _,
        Set.mem_toFinset.mpr (((B.connectedComponentMk v).mem_supp_iff v).mpr rfl)⟩
  have regionDisjoint : ((Finset.univ : Finset Large) : Set Large).PairwiseDisjoint
      (fun C => C.val.supp.toFinset) := by
    intro C _ D _ different
    apply Finset.disjoint_left.mpr
    intro v hc hd
    exact different (Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (Set.mem_toFinset.mp hc) (Set.mem_toFinset.mp hd)))
  have partSubset (C : Large) {P : Finset V} (hP : P ∈ parts C) :
      P ⊆ C.val.supp.toFinset := by
    intro v hv
    rw [← cover C]
    exact Finset.mem_biUnion.mpr ⟨P, hP, hv⟩
  have regionSize : (∑ C : Large, Fintype.card C.val) = (Finset.univ \ U).card := by
    rw [← regionCover, Finset.card_biUnion regionDisjoint]
    apply Finset.sum_congr rfl
    intro C _
    exact (Set.toFinset_card C.val.supp).symm
  refine ⟨allParts, ?_, ?_, ?_, ?_⟩
  · change (Finset.univ.biUnion parts).biUnion id = _
    rw [Finset.biUnion_biUnion]
    simpa only [cover] using regionCover
  · intro P hP Q hQ different
    obtain ⟨C, _, memberP⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨D, _, memberQ⟩ := Finset.mem_biUnion.mp hQ
    by_cases same : C = D
    · subst D
      exact disjoint C memberP memberQ different
    · exact (regionDisjoint (Finset.mem_univ C) (Finset.mem_univ D) same).mono
        (partSubset C memberP) (partSubset D memberQ)
  · intro P hP
    obtain ⟨C, _, member⟩ := Finset.mem_biUnion.mp hP
    exact pieces C P member
  · calc
      M * allParts.card ≤ M * ∑ C : Large, (parts C).card :=
        Nat.mul_le_mul_left M Finset.card_biUnion_le
      _ = ∑ C : Large, M * (parts C).card := Finset.mul_sum _ _ _
      _ ≤ ∑ C : Large, 2 * Fintype.card C.val :=
        Finset.sum_le_sum (fun C _ => count C)
      _ = 2 * (Finset.univ \ U).card := by rw [← Finset.mul_sum, regionSize]

theorem exists_large_component_partition (degree : ∀ v, B.degree v ≤ 3)
    (M : ℕ) (positive : 0 < M) (U : Finset V)
    (small_iff : ∀ v, v ∈ U ↔ Fintype.card (B.connectedComponentMk v) ≤ M) :
    ∃ parts : Finset (Finset V), parts.biUnion id = Finset.univ \ U ∧
      (parts : Set (Finset V)).Pairwise Disjoint ∧
      (∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected ∧ P.card ≤ 3 * M) ∧
      M * parts.card ≤ 2 * (Finset.univ \ U).card := by
  apply assemble_component_partitions B M U small_iff
  intro C large
  have componentDegree (v : C) : C.toSimpleGraph.degree v ≤ 3 := by
    change (B.induce C.supp).degree v ≤ 3
    rw [B.degree_induce_of_neighborSet_subset
      (fun w hw => C.mem_supp_of_adj_mem_supp v.property hw)]
    exact degree v.val
  obtain ⟨parts, cover, disjoint, pieces, count⟩ :=
    ConnectedPartition.Internal.exists_partition C.toSimpleGraph C.connected_toSimpleGraph
      componentDegree M positive large
  have componentCover : parts.biUnion id = Finset.univ := by
    simpa only [Finset.ext_iff, Finset.mem_biUnion, Finset.mem_univ] using cover
  exact lift_component_partition B M C parts componentCover disjoint pieces count

end Algebraic.Cutwidth.Bisection.RedBlack.Internal
