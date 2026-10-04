/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Matching.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Finset.Powerset

/-!
# Maximal pairing of exact-two conjunction gates

A maximum-cardinality pairing leaves gates whose two-element primary supports
are pairwise disjoint. Counting those supports bounds the unmatched remainder.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Shared

open scoped BigOperators

variable {n g : ℕ} {p : Program signature n g}

/-- Membership gives the conjunction form and exact primary cardinality. -/
theorem mem_exactTwo {i : Fin g} : i ∈ exactTwo p ↔
    (p.lines i).op.isConjunction = true ∧ (primaryInputs (p.lines i)).card = 2 := by
  simp [exactTwo]

/-- Every paired gate belongs to the exact-two family. -/
theorem PrimaryPairing.used_subset (P : PrimaryPairing p) : P.used ⊆ exactTwo p := by
  intro i hi
  obtain ⟨e, he, hi⟩ := Finset.mem_biUnion.mp hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact (P.eligible e he).1
  · have same := Finset.mem_singleton.mp hi
    subst i
    exact (P.eligible e he).2

/-- Pairwise disjoint endpoints count exactly twice the number of pairs. -/
theorem PrimaryPairing.card_used (P : PrimaryPairing p) :
    P.used.card = 2 * P.pairs.card := by
  rw [PrimaryPairing.used, Finset.card_biUnion P.disjoint]
  have same : ∀ e ∈ P.pairs, ({e.1, e.2} : Finset (Fin g)).card = 2 := by
    intro e he
    simp [P.distinct e he]
  simp_rw [Finset.sum_congr rfl same]
  simp [Nat.mul_comm]

/-- A remaining gate is not an endpoint of a selected pair. -/
theorem PrimaryPairing.not_mem_used (P : PrimaryPairing p) {i : Fin g}
    (hi : i ∈ P.remaining) : i ∉ P.used := (Finset.mem_sdiff.mp hi).2

private theorem endpoints_disjoint (P : PrimaryPairing p) {i j : Fin g}
    (hi : i ∈ P.remaining) (hj : j ∈ P.remaining) (e : Fin g × Fin g)
    (he : e ∈ P.pairs) : Disjoint ({i, j} : Finset (Fin g)) {e.1, e.2} := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have used : a ∈ P.used := Finset.mem_biUnion.mpr ⟨e, he, hb⟩
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact P.not_mem_used hi used
  · have same := Finset.mem_singleton.mp ha
    subst a
    exact P.not_mem_used hj used

private def insertPair (P : PrimaryPairing p) {i j : Fin g}
    (hi : i ∈ P.remaining) (hj : j ∈ P.remaining) (hne : i ≠ j)
    (overlap : ∃ v, v ∈ primaryInputs (p.lines i) ∧ v ∈ primaryInputs (p.lines j)) :
    PrimaryPairing p where
  pairs := insert (i, j) P.pairs
  eligible := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨(Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hj).1⟩
    · exact P.eligible e he
  distinct := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hne
    · exact P.distinct e he
  overlap := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact overlap
    · exact P.overlap e he
  disjoint := by
    intro e he f hf different
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (different rfl).elim
      · exact endpoints_disjoint P hi hj f hf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact (endpoints_disjoint P hi hj e he).symm
      · exact P.disjoint he hf different

/-- A pairing with disjoint remaining primary supports always exists. -/
theorem exists_pairing_disjoint_remaining (p : Program signature n g) :
    ∃ P : PrimaryPairing p, (P.remaining : Set (Fin g)).Pairwise fun i j =>
      Disjoint (primaryInputs (p.lines i)) (primaryInputs (p.lines j)) := by
  classical
  let candidates := (Finset.univ : Finset (Fin g × Fin g)).powerset.filter
    fun edges => ∃ P : PrimaryPairing p, P.pairs = edges
  have nonempty : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
    exact ⟨⟨∅, by simp, by simp, by simp, by simp⟩, rfl⟩
  obtain ⟨edges, hedge, maximal⟩ := candidates.exists_max_image Finset.card nonempty
  obtain ⟨P, rfl⟩ := (Finset.mem_filter.mp hedge).2
  refine ⟨P, ?_⟩
  intro i hi j hj different
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  let Q := insertPair P hi hj different ⟨v, hvi, hvj⟩
  have member : Q.pairs ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨by simp, ⟨Q, rfl⟩⟩
  have fresh : (i, j) ∉ P.pairs := by
    intro h
    apply P.not_mem_used hi
    exact Finset.mem_biUnion.mpr ⟨(i, j), h, by simp⟩
  have bound := maximal Q.pairs member
  change (insert (i, j) P.pairs).card ≤ P.pairs.card at bound
  rw [Finset.card_insert_of_notMem fresh] at bound
  lia

/-- Disjoint two-element supports leave at most half as many gates as inputs. -/
theorem PrimaryPairing.card_remaining_le (P : PrimaryPairing p)
    (disjoint : (P.remaining : Set (Fin g)).Pairwise fun i j =>
      Disjoint (primaryInputs (p.lines i)) (primaryInputs (p.lines j))) :
    P.remaining.card ≤ n / 2 := by
  have card : (P.remaining.biUnion fun i => primaryInputs (p.lines i)).card =
      2 * P.remaining.card := by
    rw [Finset.card_biUnion disjoint]
    have same : ∀ i ∈ P.remaining, (primaryInputs (p.lines i)).card = 2 := by
      intro i hi
      exact (mem_exactTwo.mp (Finset.mem_sdiff.mp hi).1).2
    simp_rw [Finset.sum_congr rfl same]
    simp [Nat.mul_comm]
  have bound := Finset.card_le_univ (P.remaining.biUnion fun i => primaryInputs (p.lines i))
  rw [card, Fintype.card_fin] at bound
  lia

/-- The exact-two count splits into twice the pair count and the remainder. -/
theorem PrimaryPairing.card_exactTwo (P : PrimaryPairing p) :
    (exactTwo p).card = 2 * P.pairs.card + P.remaining.card := by
  have split := Finset.card_sdiff_add_card_eq_card P.used_subset
  rw [P.card_used] at split
  change P.remaining.card + 2 * P.pairs.card = (exactTwo p).card at split
  lia

end Algebraic.Aggregate.Geometry.Shared
