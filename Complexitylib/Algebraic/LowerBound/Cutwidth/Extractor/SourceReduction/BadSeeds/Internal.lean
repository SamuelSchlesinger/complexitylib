/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.BadSeeds.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Counting low-order parity tests and their bad seeds

Every nonempty set of at most `t` coordinates is the range of a `t`-tuple:
enumerate it and repeat any member in the spare positions. The number of
tuples therefore bounds the number of tests, including at zero coordinates
or zero order. Two finite union bounds then control the common bad-seed set.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem exists_tuple_image {ι : Type*} (U : Finset ι) {t : Nat}
    (hne : U.Nonempty) (hcard : U.card ≤ t) :
    ∃ f : Fin t → ι, Finset.univ.image f = U := by
  obtain ⟨a, ha⟩ := hne
  let f : Fin t → ι := fun i =>
    if hi : i.val < U.card then (U.equivFin.symm ⟨i.val, hi⟩).val else a
  refine ⟨f, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [f]
    split
    · exact (U.equivFin.symm _).property
    · exact ha
  · intro hx
    let j := U.equivFin ⟨x, hx⟩
    refine Finset.mem_image.mpr ⟨⟨j.val, j.isLt.trans_le hcard⟩, Finset.mem_univ _, ?_⟩
    dsimp only [f]
    rw [dite_eq_left j.isLt]
    exact congrArg Subtype.val (U.equivFin.symm_apply_apply ⟨x, hx⟩)

theorem card_parityTests_le_pow (ι : Type*) [Fintype ι] (t : Nat) :
    (parityTests ι t).card ≤ Fintype.card ι ^ t := by
  have inside : parityTests ι t ⊆
      Finset.univ.image (fun f : Fin t → ι => Finset.univ.image f) := by
    intro U hU
    obtain ⟨hne, hcard⟩ := (Finset.mem_filter.mp hU).2
    obtain ⟨f, hf⟩ := exists_tuple_image U hne hcard
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, hf⟩
  calc
    (parityTests ι t).card ≤
        (Finset.univ.image (fun f : Fin t → ι => Finset.univ.image f)).card :=
      Finset.card_le_card inside
    _ ≤ Fintype.card (Fin t → ι) := Finset.card_image_le
    _ = Fintype.card ι ^ t := Fintype.card_pi_const ι t

theorem card_parityBadSeeds_le {ι Choice Seed : Type*} [Fintype ι] [Fintype Choice]
    [Fintype Seed] (bad : Finset ι → Choice → Finset Seed) (t : Nat)
    {η : ℝ} (hη : 0 ≤ η)
    (bound : ∀ U ∈ parityTests ι t, ∀ z,
      ((bad U z).card : ℝ) ≤ η * Fintype.card Seed) :
    ((parityBadSeeds bad t).card : ℝ) ≤
      (Fintype.card ι : ℝ) ^ t * Fintype.card Choice * η * Fintype.card Seed := by
  have tests : ((parityTests ι t).card : ℝ) ≤ (Fintype.card ι : ℝ) ^ t := by
    exact_mod_cast card_parityTests_le_pow ι t
  have unionBound (U : Finset ι) (hU : U ∈ parityTests ι t) :
      ((Finset.univ.biUnion (bad U)).card : ℝ) ≤
        Fintype.card Choice * (η * Fintype.card Seed) := by
    calc
      ((Finset.univ.biUnion (bad U)).card : ℝ) ≤ ∑ z, ((bad U z).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le (s := Finset.univ) (t := bad U)
      _ ≤ ∑ _z : Choice, η * Fintype.card Seed :=
        Finset.sum_le_sum fun z _ => bound U hU z
      _ = Fintype.card Choice * (η * Fintype.card Seed) := by simp
  calc
    ((parityBadSeeds bad t).card : ℝ) ≤
        ∑ U ∈ parityTests ι t, ((Finset.univ.biUnion (bad U)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
        (s := parityTests ι t) (t := fun U => Finset.univ.biUnion (bad U))
    _ ≤ ∑ _U ∈ parityTests ι t,
        Fintype.card Choice * (η * Fintype.card Seed) := Finset.sum_le_sum unionBound
    _ = (parityTests ι t).card * (Fintype.card Choice * (η * Fintype.card Seed)) := by
      simp
    _ ≤ (Fintype.card ι : ℝ) ^ t *
        (Fintype.card Choice * (η * Fintype.card Seed)) :=
      mul_le_mul_of_nonneg_right tests
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hη (Nat.cast_nonneg _)))
    _ = _ := by ring

end Algebraic.Cutwidth.Extractor.Internal
