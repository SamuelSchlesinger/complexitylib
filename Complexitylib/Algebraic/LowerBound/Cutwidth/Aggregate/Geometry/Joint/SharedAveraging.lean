/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedAveraging.Weighted
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.SharedMessage.Basic
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Shared.Matching.Defs

/-!
# A cut retaining weighted original gate classes

Pad each original two-primary support to a triple and choose a triple inside each
original wide support. Weighted averaging over fixed-size cuts then preserves the
same exact triple-retention fraction of the two different information savings.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Algebraic.Aggregate.Geometry
open scoped BigOperators Classical

/-- On the full input set, wide retention is the original three-primary gate predicate. -/
theorem retainedWide_univ_iff {n g : ℕ} (line : Line signature n g) :
    RetainedWide line Finset.univ ↔
      line.op.isConjunction = true ∧ 3 ≤ (primaryInputs line).card := by
  constructor
  · intro h
    exact ⟨h.1, by simpa [card_literalVars_lineLiterals line h.1] using h.2⟩
  · intro h
    exact ⟨h.1, by simpa [card_literalVars_lineLiterals line h.1] using h.2⟩

/-- Original exact-two and wide conjunction gates partition the multiple-primary count. -/
theorem exactTwo_add_retainedWide_univ {n g : ℕ} (p : Program signature n g) :
    (Shared.exactTwo p).card + (retainedWide p Finset.univ).card = multiCount p := by
  have partition : Shared.exactTwo p ∪ retainedWide p Finset.univ =
      Finset.univ.filter fun i => multiPrimary (p.lines i) = true := by
    ext i
    simp only [Shared.exactTwo, retainedWide, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, retainedWide_univ_iff, multiPrimary,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨h, two⟩ | ⟨h, wide⟩) <;> exact ⟨h, by lia⟩
    · rintro ⟨h, multiple⟩
      by_cases two : (primaryInputs (p.lines i)).card = 2
      · exact Or.inl ⟨h, two⟩
      · exact Or.inr ⟨h, by lia⟩
  have disjoint : Disjoint (Shared.exactTwo p) (retainedWide p Finset.univ) := by
    apply Finset.disjoint_left.mpr
    intro i ht hw
    have two := (Finset.mem_filter.mp ht).2.2
    have wide := ((retainedWide_univ_iff _).mp (Finset.mem_filter.mp hw).2).2
    lia
  rw [← Finset.card_union_of_disjoint disjoint, partition, multiCount_eq_card_filter]

private theorem card_subtype_filter_le {α : Type*} [DecidableEq α]
    (S T : Finset α) (P : S → Prop) [DecidablePred P]
    (mem : ∀ i, P i → i.val ∈ T) :
    (Finset.univ.filter P).card ≤ T.card := by
  have sub : (Finset.univ.filter P).image Subtype.val ⊆ T := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact mem j (Finset.mem_filter.mp hj).2
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using
    Finset.card_le_card sub

/-- One actual cut retains a common triple fraction of both weighted gate classes. -/
theorem exists_subset_retained_weight {n g a : ℕ} (p : Program signature n g)
    (ha : 3 ≤ a) (han : a ≤ n) (rho r : ℝ) (hrho : 0 ≤ rho) (hr : 0 ≤ r) :
    ∃ U : Finset (Fin n), U.card = a ∧
      tripleRetention n a *
          (rho * (Shared.exactTwo p).card + r * (retainedWide p Finset.univ).card) ≤
        rho * (retainedTwo p U).card + r * (retainedWide p U).card := by
  let T := Shared.exactTwo p
  let W := retainedWide p Finset.univ
  have pair (i : T) : ∃ S : Finset (Fin n),
      primaryInputs (p.lines i.val) ⊆ S ∧ S.card = 3 := by
    have two := (Finset.mem_filter.mp i.property).2.2
    obtain ⟨S, sub, _, card⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (primaryInputs (p.lines i.val))) (by lia :
        (primaryInputs (p.lines i.val)).card ≤ 3)
      (by simpa using (show 3 ≤ n by lia))
    exact ⟨S, sub, card⟩
  have wide (i : W) : ∃ S : Finset (Fin n),
      S ⊆ primaryInputs (p.lines i.val) ∧ S.card = 3 := by
    have h := (retainedWide_univ_iff _).mp (Finset.mem_filter.mp i.property).2
    exact Finset.exists_subset_card_eq h.2
  choose twoWitness twoSub twoCard using pair
  choose wideWitness wideSub wideCard using wide
  let witness : T ⊕ W → Finset (Fin n) := Sum.elim twoWitness wideWitness
  let weight : T ⊕ W → ℝ := Sum.elim (fun _ => rho) (fun _ => r)
  obtain ⟨U, hU, bound⟩ := exists_subset_weighted_triples ha han witness
    (by intro i; cases i <;> simp [witness, twoCard, wideCard]) weight
  refine ⟨U, hU, le_trans (b := ∑ j, if witness j ⊆ U then weight j else 0) ?_ ?_⟩
  · simpa [weight, Fintype.sum_sum_type, mul_comm, T, W] using bound
  have twoRetained (i : T) (h : twoWitness i ⊆ U) : i.val ∈ retainedTwo p U := by
    have original := (Finset.mem_filter.mp i.property).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, original.1, original.2,
      (twoSub i).trans h⟩
  have wideRetained (i : W) (h : wideWitness i ⊆ U) : i.val ∈ retainedWide p U := by
    have original := (retainedWide_univ_iff _).mp (Finset.mem_filter.mp i.property).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, original.1, ?_⟩
    rw [card_literalVars_lineLiterals _ original.1]
    have sub : wideWitness i ⊆ primaryInputs (p.lines i.val) ∩ U :=
      Finset.subset_inter (wideSub i) h
    simpa only [wideCard] using Finset.card_le_card sub
  have countT := card_subtype_filter_le T (retainedTwo p U)
    (fun i => twoWitness i ⊆ U) twoRetained
  have countW := card_subtype_filter_le W (retainedWide p U)
    (fun i => wideWitness i ⊆ U) wideRetained
  have sumT : (∑ i : T, if twoWitness i ⊆ U then rho else 0) =
      rho * (Finset.univ.filter fun i => twoWitness i ⊆ U).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have sumW : (∑ i : W, if wideWitness i ⊆ U then r else 0) =
      r * (Finset.univ.filter fun i => wideWitness i ⊆ U).card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [Fintype.sum_sum_type]
  change (∑ i : T, if twoWitness i ⊆ U then rho else 0) +
    (∑ i : W, if wideWitness i ⊆ U then r else 0) ≤ _
  rw [sumT, sumW]
  exact add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast countT) hrho)
    (mul_le_mul_of_nonneg_left (by exact_mod_cast countW) hr)

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
