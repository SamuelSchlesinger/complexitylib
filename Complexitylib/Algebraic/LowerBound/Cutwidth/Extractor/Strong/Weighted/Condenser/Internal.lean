/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.FlatMixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Internal
import Mathlib.Algebra.BigOperators.Field

/-!
# From flat lossless witnesses to weighted strong condensation

Decompose the input into exact-size flat sources. For each component and
seed, push uniform weights through the supplied injection. Their mixture
is normalized and preserves the point-mass cap at every seed. Linearity of
joint tests transfers the common error, and the equal-mass test criterion
converts it to total variation.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

private theorem probabilityWeight_mixture {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (w : ι → ℝ) (q : ι → Ω → ℝ) (nonnegative : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1)
    (probability : ∀ i, IsProbabilityWeight (q i)) :
    IsProbabilityWeight (fun z => ∑ i, w i * q i z) := by
  refine ⟨fun z => Finset.sum_nonneg fun i _ =>
    mul_nonneg (nonnegative i) ((probability i).1 z), ?_⟩
  rw [Finset.sum_comm]
  have totals (i : ι) : ∑ z, q i z = 1 := (probability i).2
  simpa only [← Finset.mul_sum, totals, mul_one] using mass

private theorem cappedWeight_mixture {ι Ω : Type*} [Fintype ι]
    (w : ι → ℝ) (q : ι → Ω → ℝ) (nonnegative : ∀ i, 0 ≤ w i) (mass : ∑ i, w i = 1)
    {K : Nat} (cap : ∀ i, CappedWeight (q i) K) :
    CappedWeight (fun z => ∑ i, w i * q i z) K := by
  intro z
  calc
    _ = ∑ i, w i * ((K : ℝ) * q i z) := by
      rw [Finset.mul_sum]
      simp only [mul_left_comm (K : ℝ)]
    _ ≤ ∑ i, w i * 1 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (cap i z) (nonnegative i)
    _ = 1 := by simpa only [mul_one] using mass

theorem weightedStrongSeededCondenser_of_weightedStrong {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) :
    WeightedStrongSeededCondenser E K (Fintype.card Ω) ε := by
  intro p probability cap
  have uniform := isProbabilityWeight_uniform Ω
  refine ⟨fun _ => uniformWeight Ω, fun _ => uniform, ?_, ?_⟩
  · intro y z
    have nonzero : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (mul_inv_cancel₀ nonzero).le
  · have actual := probabilityWeight_weightedSeededOutput probability E
    have ideal := probabilityWeight_seedFamilyWeight (fun _ : Seed => uniformWeight Ω)
      (fun _ => uniform)
    apply (weightDist_le_iff_tests _ _ (actual.2.trans ideal.2.symm)).mpr
    intro T
    rw [weightTestProb_weightedSeededOutput, weightTestProb_seedFamilyWeight_uniform]
    exact extract p probability cap T

theorem weightedStrongSeededCondenser_of_flat_injections {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed]
    (C : α → Seed → Ω) {K : Nat} (positive : 0 < K) {ε : ℝ}
    (flat : ∀ P : Finset α, P.card = K →
      ∃ g : Seed → (P ↪ Ω), ∀ T : Finset (Seed × Ω),
        |seededTestProb (fun x : P => C x.val) T -
          seededTestProb (fun x y => g y x) T| ≤ ε) :
    WeightedStrongSeededCondenser C K K ε := by
  intro p probability cap
  obtain ⟨w, nonnegative, mass, mixture⟩ :=
    exists_flat_mixture_of_capped_weights p positive probability.1 probability.2 cap
  choose g close using fun S : {S : Finset α // S.card = K} => flat S.val S.property
  let family (S : {S : Finset α // S.card = K}) (y : Seed) : Ω → ℝ :=
    mapWeight (g S y) (uniformWeight S.val)
  have family_probability (S : {S : Finset α // S.card = K}) (y : Seed) :
      IsProbabilityWeight (family S y) := by
    let : Nonempty S.val := Fintype.card_pos_iff.mp
      (by simpa only [Fintype.card_coe, S.property] using positive)
    exact (isProbabilityWeight_uniform S.val).map (g S y)
  have family_cap (S : {S : Finset α // S.card = K}) (y : Seed) :
      CappedWeight (family S y) K := by
    apply cappedWeight_map_injective _ (g S y) (g S y).injective
    intro x
    have nonzero : (K : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
    simpa only [uniformWeight, Fintype.card_coe, S.property] using
      (mul_inv_cancel₀ nonzero).le
  let q (y : Seed) (z : Ω) : ℝ := ∑ S, w S * family S y z
  have q_probability (y : Seed) : IsProbabilityWeight (q y) :=
    probabilityWeight_mixture w (fun S => family S y) nonnegative mass
      (fun S => family_probability S y)
  have q_cap (y : Seed) : CappedWeight (q y) K :=
    cappedWeight_mixture w (fun S => family S y) nonnegative mass (fun S => family_cap S y)
  refine ⟨q, q_probability, q_cap, ?_⟩
  have actual := probabilityWeight_weightedSeededOutput probability C
  have ideal := probabilityWeight_seedFamilyWeight q q_probability
  apply (weightDist_le_iff_tests _ _ (actual.2.trans ideal.2.symm)).mpr
  intro T
  have identity : p = fun x => ∑ S : {S : Finset α // S.card = K}, w S * flatWeight S.val x := by
    funext x
    have card (S : {S : Finset α // S.card = K}) : S.val.card = K := S.property
    simpa only [flatWeight, card] using mixture x
  have family_test (S : {S : Finset α // S.card = K}) :
      weightTestProb (seedFamilyWeight (family S)) T =
        seededTestProb (fun x y => g S y x) T := by
    change weightTestProb
      (weightedSeededOutput (uniformWeight S.val) (fun x y => g S y x)) T = _
    rw [weightTestProb_weightedSeededOutput, weightedSeededTestProb_uniformWeight]
  rw [weightTestProb_weightedSeededOutput]
  change |weightedSeededTestProb p C T -
    weightTestProb (seedFamilyWeight (fun y z => ∑ S, w S * family S y z)) T| ≤ ε
  rw [identity, weightedSeededTestProb_mixture, weightTestProb_seedFamilyWeight_mixture]
  apply abs_mixture_sub_le w _ _ nonnegative mass
  intro S
  rw [weightedSeededTestProb_flatWeight, family_test]
  exact close S T

end Algebraic.Cutwidth.Extractor.Internal
