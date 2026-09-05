/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
import Complexitylib.Classes.AverageCase.Ensemble.Internal
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Finite uniform-seed distribution ensembles -- proof internals

The generic finite probability laws are proved by exact cardinal arithmetic.
Ensemble laws then instantiate them with each slice's explicit nonempty seed
space.
-/


public section

universe u v w

namespace Complexity

theorem uniformProbability_nonneg_internal {Ω : Type u} [Fintype Ω]
    (event : Finset Ω) :
    0 ≤ uniformProbability event := by
  unfold uniformProbability
  positivity

theorem uniformProbability_le_one_internal {Ω : Type u}
    [Fintype Ω] [Nonempty Ω] (event : Finset Ω) :
    uniformProbability event ≤ 1 := by
  have hden : ((Fintype.card Ω : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hcard : (event.card : ℚ) ≤ Fintype.card Ω := by
    exact_mod_cast Finset.card_le_univ event
  calc
    uniformProbability event = (event.card : ℚ) / Fintype.card Ω := rfl
    _ ≤ (Fintype.card Ω : ℚ) / Fintype.card Ω := by gcongr
    _ = 1 := div_self hden

theorem uniformProbability_empty_internal {Ω : Type u}
    [Fintype Ω] :
    uniformProbability (∅ : Finset Ω) = 0 := by
  simp [uniformProbability]

theorem uniformProbability_univ_internal {Ω : Type u}
    [Fintype Ω] [Nonempty Ω] :
    uniformProbability (Finset.univ : Finset Ω) = 1 := by
  have hden : ((Fintype.card Ω : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  simp [uniformProbability, hden]

theorem uniformProbability_compl_internal {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] (event : Finset Ω) :
    uniformProbability eventᶜ = 1 - uniformProbability event := by
  have hcard : event.card ≤ Fintype.card Ω := Finset.card_le_univ event
  have hden : ((Fintype.card Ω : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  unfold uniformProbability
  rw [Finset.card_compl, Nat.cast_sub hcard, sub_div, div_self hden]

theorem uniformProbability_union_le_internal {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (event₁ event₂ : Finset Ω) :
    uniformProbability (event₁ ∪ event₂) ≤
      uniformProbability event₁ + uniformProbability event₂ := by
  unfold uniformProbability
  rw [← add_div]
  gcongr
  exact_mod_cast Finset.card_union_le event₁ event₂

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem uniformProbability_eq_sum_fiberwise_internal
    {Ω : Type u} {ι : Type v} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq ι] (event : Finset Ω) (indices : Finset ι) (f : Ω → ι)
    (hmaps : (event : Set Ω).MapsTo f indices) :
    uniformProbability event =
      ∑ i ∈ indices,
        uniformProbability (event.filter fun seed => f seed = i) := by
  unfold uniformProbability
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  rw [Finset.sum_div]

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem uniformProbability_product_internal
    {Ω : Type u} {Ξ : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype Ξ] [DecidableEq Ξ] (P : Ω → Prop) (Q : Ξ → Prop)
    [DecidablePred P] [DecidablePred Q] :
    uniformProbability
        (Finset.univ.filter fun seed : Ω × Ξ => P seed.1 ∧ Q seed.2) =
      uniformProbability (Finset.univ.filter P) *
        uniformProbability (Finset.univ.filter Q) := by
  have hevent :
      (Finset.univ.filter fun seed : Ω × Ξ => P seed.1 ∧ Q seed.2) =
        (Finset.univ.filter P).product (Finset.univ.filter Q) := by
    ext seed
    simp
  rw [hevent]
  unfold uniformProbability
  rw [show
    ((Finset.univ.filter P).product (Finset.univ.filter Q)).card =
      (Finset.univ.filter P).card * (Finset.univ.filter Q).card from
    Finset.card_product _ _]
  simp only [Fintype.card_prod]
  push_cast
  exact (div_mul_div_comm
    ((Finset.univ.filter P).card : ℚ) (Fintype.card Ω : ℚ)
    ((Finset.univ.filter Q).card : ℚ) (Fintype.card Ξ : ℚ)).symm

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem uniformProbability_product_eq_average_fibers_internal
    {advice : Type u} {challenge : Type v}
    [Fintype advice] [DecidableEq advice] [Nonempty advice]
    [Fintype challenge] [DecidableEq challenge] [Nonempty challenge]
    (event : advice → challenge → Prop)
    [DecidablePred fun sample : advice × challenge =>
      event sample.1 sample.2]
    [∀ fixed, DecidablePred (event fixed)] :
    uniformProbability (Finset.univ.filter fun sample : advice × challenge =>
        event sample.1 sample.2) =
      (∑ fixed : advice,
        uniformProbability (Finset.univ.filter (event fixed))) /
        Fintype.card advice := by
  classical
  unfold uniformProbability
  have hcard :
      (Finset.univ.filter fun sample : advice × challenge =>
        event sample.1 sample.2).card =
        ∑ fixed : advice, (Finset.univ.filter (event fixed)).card := by
    calc
      (Finset.univ.filter fun sample : advice × challenge =>
          event sample.1 sample.2).card =
          ∑ sample ∈ (Finset.univ : Finset (advice × challenge)),
            if event sample.1 sample.2 then 1 else 0 := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ fixed ∈ (Finset.univ : Finset advice),
          ∑ input ∈ (Finset.univ : Finset challenge),
            if event fixed input then 1 else 0 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ fixed : advice,
          (Finset.univ.filter (event fixed)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcard, Fintype.card_prod]
  push_cast
  rw [Finset.sum_div]
  have hadvice : (Fintype.card advice : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hchallenge : (Fintype.card challenge : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  field_simp [hadvice, hchallenge]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro fixed _hfixed
  field_simp [hadvice, hchallenge]

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem exists_fiber_uniformProbability_ge_internal
    {advice : Type u} {challenge : Type v}
    [Fintype advice] [DecidableEq advice] [Nonempty advice]
    [Fintype challenge] [DecidableEq challenge] [Nonempty challenge]
    (event : advice → challenge → Prop)
    [DecidablePred fun sample : advice × challenge =>
      event sample.1 sample.2]
    [∀ fixed, DecidablePred (event fixed)] :
    ∃ fixed : advice,
      uniformProbability (Finset.univ.filter fun sample : advice × challenge =>
          event sample.1 sample.2) ≤
        uniformProbability (Finset.univ.filter (event fixed)) := by
  classical
  let overall := uniformProbability
    (Finset.univ.filter fun sample : advice × challenge =>
      event sample.1 sample.2)
  have hadvice : (Fintype.card advice : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hsum :
      ∑ _fixed : advice, overall ≤
        ∑ fixed : advice,
          uniformProbability (Finset.univ.filter (event fixed)) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [overall]
    rw [uniformProbability_product_eq_average_fibers_internal event]
    field_simp [hadvice]
    exact le_rfl
  obtain ⟨fixed, _hfixed, hle⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty : (Finset.univ : Finset advice).Nonempty) hsum
  exact ⟨fixed, hle⟩

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem uniformMean_le_threshold_add_probability_internal
    {sample : Type u} [Fintype sample] [DecidableEq sample]
    [Nonempty sample] (value : sample → ℚ) (threshold : ℚ)
    (hupper : ∀ input, value input ≤ 1) :
    uniformMean value ≤ threshold +
      uniformProbability (Finset.univ.filter fun input =>
        threshold ≤ value input) * (1 - threshold) := by
  classical
  let good := Finset.univ.filter fun input : sample => threshold ≤ value input
  let bad := Finset.univ.filter fun input : sample => ¬threshold ≤ value input
  have hgood : ∑ input ∈ good, value input ≤ (good.card : ℚ) := by
    have h := Finset.sum_le_card_nsmul good value (1 : ℚ)
      (fun input _hinput => hupper input)
    simpa [nsmul_eq_mul] using h
  have hbad :
      ∑ input ∈ bad, value input ≤ (bad.card : ℚ) * threshold := by
    have h := Finset.sum_le_card_nsmul bad value threshold (by
      intro input hinput
      have hnot : ¬threshold ≤ value input := by
        simpa [bad] using hinput
      exact le_of_lt (lt_of_not_ge hnot))
    simpa [nsmul_eq_mul] using h
  have hsum :
      ∑ input : sample, value input ≤
        (good.card : ℚ) + (bad.card : ℚ) * threshold := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun input => threshold ≤ value input) value]
    exact add_le_add hgood hbad
  have hcardNat : good.card + bad.card = Fintype.card sample := by
    simpa [good, bad] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset sample))
        (fun input => threshold ≤ value input))
  have hcard :
      (good.card : ℚ) + (bad.card : ℚ) = Fintype.card sample := by
    exact_mod_cast hcardNat
  have hden : (0 : ℚ) < Fintype.card sample := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  unfold uniformMean uniformProbability
  change (∑ input : sample, value input) / Fintype.card sample ≤
    threshold + (good.card : ℚ) / Fintype.card sample * (1 - threshold)
  apply (div_le_iff₀ hden).2
  calc
    ∑ input : sample, value input ≤
        (good.card : ℚ) + (bad.card : ℚ) * threshold := hsum
    _ = (threshold + (good.card : ℚ) / Fintype.card sample *
          (1 - threshold)) * Fintype.card sample := by
      field_simp
      rw [← hcard]
      ring

theorem uniformMean_sub_div_le_probability_ge_internal
    {sample : Type u} [Fintype sample] [DecidableEq sample]
    [Nonempty sample] (value : sample → ℚ) (lower threshold : ℚ)
    (hupper : ∀ input, value input ≤ 1)
    (hlower : lower ≤ uniformMean value) (hthreshold : threshold < 1) :
    (lower - threshold) / (1 - threshold) ≤
      uniformProbability (Finset.univ.filter fun input =>
        threshold ≤ value input) := by
  have hmean :=
    (hlower.trans <|
      uniformMean_le_threshold_add_probability_internal
        value threshold hupper)
  apply (div_le_iff₀ (sub_pos.mpr hthreshold)).2
  linarith

theorem half_epsilon_le_probability_ge_of_le_uniformMean_internal
    {sample : Type u} [Fintype sample] [DecidableEq sample]
    [Nonempty sample] (value : sample → ℚ) (epsilon : ℚ)
    (hepsilon : 0 ≤ epsilon) (hupper : ∀ input, value input ≤ 1)
    (hmean : 1 / 2 + epsilon ≤ uniformMean value) :
    epsilon / 2 ≤
      uniformProbability (Finset.univ.filter fun input =>
        1 / 2 + epsilon / 2 ≤ value input) := by
  let probability := uniformProbability
    (Finset.univ.filter fun input : sample =>
      1 / 2 + epsilon / 2 ≤ value input)
  have hprobability : 0 ≤ probability := uniformProbability_nonneg_internal _
  have hmeanUpper := uniformMean_le_threshold_add_probability_internal
    value (1 / 2 + epsilon / 2) hupper
  change uniformMean value ≤ 1 / 2 + epsilon / 2 +
    probability * (1 - (1 / 2 + epsilon / 2)) at hmeanUpper
  have hfactor :
      probability * (1 - (1 / 2 + epsilon / 2)) ≤ probability := by
    nlinarith
  nlinarith

theorem uniformAtLeastOneProbability_eq_one_sub_pow_internal
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) :
    uniformAtLeastOneProbability event trials =
      1 - (1 - uniformProbability event) ^ trials := by
  classical
  let success := uniformAtLeastOneEvent event trials
  let failure := Finset.univ.filter fun draws : Fin trials → Ω =>
    ∀ trial, draws trial ∉ event
  have hcompl : successᶜ = failure := by
    ext draws
    simp [success, failure, uniformAtLeastOneEvent]
  have hfailureCard : failure.card = eventᶜ.card ^ trials := by
    have hfailure : failure =
        Fintype.piFinset (fun _trial : Fin trials => eventᶜ) := by
      ext draws
      simp [failure]
    rw [hfailure, Fintype.card_piFinset]
    simp
  have hfailureProbability :
      uniformProbability failure =
        uniformProbability eventᶜ ^ trials := by
    unfold uniformProbability
    rw [hfailureCard, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [div_pow]
  have hsuccessFailure :
      uniformProbability success = 1 - uniformProbability failure := by
    have h := uniformProbability_compl_internal success
    rw [hcompl] at h
    linarith
  change uniformProbability success = _
  rw [hsuccessFailure, hfailureProbability,
    uniformProbability_compl_internal event]

theorem one_sub_pow_le_uniformAtLeastOneProbability_internal
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤ uniformProbability event) :
    1 - (1 - singleDrawLower) ^ trials ≤
      uniformAtLeastOneProbability event trials := by
  rw [uniformAtLeastOneProbability_eq_one_sub_pow_internal]
  have hnonneg : 0 ≤ 1 - uniformProbability event :=
    sub_nonneg.mpr (uniformProbability_le_one_internal event)
  have hpow :
      (1 - uniformProbability event) ^ trials ≤
        (1 - singleDrawLower) ^ trials :=
    pow_le_pow_left₀ hnonneg (sub_le_sub_left hlower 1) trials
  linarith

private theorem pow_one_sub_le_one_div_one_add_nat_mul
    (probability : ℚ) (hnonneg : 0 ≤ probability)
    (hleOne : probability ≤ 1) (trials : ℕ) :
    (1 - probability) ^ trials ≤
      1 / (1 + (trials : ℚ) * probability) := by
  induction trials with
  | zero => simp
  | succ trials ih =>
      have hden : 0 < 1 + (trials : ℚ) * probability := by positivity
      have hdenSucc : 0 < 1 + (trials.succ : ℚ) * probability := by
        positivity
      rw [pow_succ]
      calc
        (1 - probability) ^ trials * (1 - probability) ≤
            (1 / (1 + (trials : ℚ) * probability)) *
              (1 - probability) := by
          exact mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hleOne)
        _ ≤ 1 / (1 + (trials.succ : ℚ) * probability) := by
          rw [le_div_iff₀ hdenSucc]
          field_simp [hden.ne']
          push_cast
          have hterm :
              0 ≤ ((trials : ℚ) + 1) * probability ^ 2 := by
            positivity
          nlinarith

theorem trials_mul_div_one_add_le_uniformAtLeastOneProbability_internal
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) :
    (trials : ℚ) * uniformProbability event /
        (1 + (trials : ℚ) * uniformProbability event) ≤
      uniformAtLeastOneProbability event trials := by
  let probability := uniformProbability event
  have hnonneg : 0 ≤ probability := uniformProbability_nonneg_internal event
  have hleOne : probability ≤ 1 := uniformProbability_le_one_internal event
  have hden : 0 < 1 + (trials : ℚ) * probability := by positivity
  have hpow := pow_one_sub_le_one_div_one_add_nat_mul
    probability hnonneg hleOne trials
  rw [uniformAtLeastOneProbability_eq_one_sub_pow_internal]
  change (trials : ℚ) * probability /
      (1 + (trials : ℚ) * probability) ≤ 1 - (1 - probability) ^ trials
  calc
    (trials : ℚ) * probability /
          (1 + (trials : ℚ) * probability) =
        1 - 1 / (1 + (trials : ℚ) * probability) := by
      field_simp [hden.ne']
      ring
    _ ≤ 1 - (1 - probability) ^ trials := sub_le_sub_left hpow 1

theorem half_le_uniformAtLeastOneProbability_of_singleDrawLower_internal
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤ uniformProbability event)
    (htrials : 1 ≤ (trials : ℚ) * singleDrawLower) :
    1 / 2 ≤ uniformAtLeastOneProbability event trials := by
  have heventNonneg : 0 ≤ uniformProbability event :=
    uniformProbability_nonneg_internal event
  have hden :
      0 < 1 + (trials : ℚ) * uniformProbability event := by
    positivity
  refine le_trans ?_
    (trials_mul_div_one_add_le_uniformAtLeastOneProbability_internal
      event trials)
  rw [le_div_iff₀ hden]
  have hmul :
      1 ≤ (trials : ℚ) * uniformProbability event :=
    htrials.trans <| mul_le_mul_of_nonneg_left hlower (by positivity)
  nlinarith

-- The signature mirrors the family this belongs to; the argument is part of
-- that shape even where this member does not consult it.
@[nolint unusedArguments]
theorem uniformProbability_equiv_internal
    {Ω : Type u} {Ξ : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype Ξ] [DecidableEq Ξ] (e : Ω ≃ Ξ) (P : Ξ → Prop)
    [DecidablePred P] :
    uniformProbability (Finset.univ.filter fun x : Ω => P (e x)) =
      uniformProbability (Finset.univ.filter P) := by
  have hcard :
      (Finset.univ.filter fun x : Ω => P (e x)).card =
        (Finset.univ.filter P).card := by
    apply Finset.card_bij' (fun x _ => e x) (fun y _ => e.symm y)
    · intro x hx
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · intro y hy
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using hy
    · intro x _
      exact e.symm_apply_apply x
    · intro y _
      exact e.apply_symm_apply y
  unfold uniformProbability
  rw [hcard, Fintype.card_congr e]

theorem uniformProbability_eq_internal {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (x : Ω) :
    uniformProbability (Finset.univ.filter fun y : Ω => y = x) =
      1 / Fintype.card Ω := by
  unfold uniformProbability
  rw [show Finset.univ.filter (fun y : Ω => y = x) = {x} by
    ext y
    simp]
  simp

namespace FiniteEnsemble

variable {α : Type u} {β : Type w}

theorem probability_nonneg_internal (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    0 ≤ D.probability n P := by
  let := D.seedFintype n
  exact uniformProbability_nonneg_internal _

theorem probability_le_one_internal (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n P ≤ 1 := by
  let := D.seedFintype n
  let := D.seedNonempty n
  exact uniformProbability_le_one_internal _

theorem probability_false_internal (D : FiniteEnsemble α) (n : ℕ) :
    D.probability n (fun _ => False) = 0 := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  simp [probability, event, uniformProbability_empty_internal]

theorem probability_true_internal (D : FiniteEnsemble α) (n : ℕ) :
    D.probability n (fun _ => True) = 1 := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  let := D.seedNonempty n
  simp [probability, event, uniformProbability_univ_internal]

theorem probability_not_internal (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n (fun x => ¬ P x) = 1 - D.probability n P := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  let := D.seedNonempty n
  have hevent : D.event n (fun x => ¬ P x) = (D.event n P)ᶜ := by
    ext seed
    simp [event]
  rw [probability, hevent, uniformProbability_compl_internal]
  rfl

theorem probability_or_le_internal (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    D.probability n (fun x => P x ∨ Q x) ≤
      D.probability n P + D.probability n Q := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  have hevent : D.event n (fun x => P x ∨ Q x) = D.event n P ∪ D.event n Q := by
    ext seed
    simp [event]
  rw [probability, hevent]
  exact uniformProbability_union_le_internal _ _

theorem probability_mono_internal (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) :
    D.probability n P ≤ D.probability n Q := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  unfold probability uniformProbability
  gcongr
  intro seed hseed
  rw [show D.event n P =
      Finset.univ.filter (fun seed => P (D.sample n seed)) from rfl] at hseed
  rw [show D.event n Q =
      Finset.univ.filter (fun seed => Q (D.sample n seed)) from rfl]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseed ⊢
  exact hPQ _ hseed

theorem probability_congr_internal (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x ↔ Q x) :
    D.probability n P = D.probability n Q := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  unfold probability
  apply congrArg uniformProbability
  ext seed
  rw [show D.event n P =
      Finset.univ.filter (fun seed => P (D.sample n seed)) from rfl]
  rw [show D.event n Q =
      Finset.univ.filter (fun seed => Q (D.sample n seed)) from rfl]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hPQ _

theorem probability_map_internal (D : FiniteEnsemble α) (f : α → β)
    (n : ℕ) (P : β → Prop) [DecidablePred P] :
    (D.map f).probability n P = D.probability n (fun x => P (f x)) := by
  rfl

theorem sum_mass_eq_one_internal [DecidableEq α]
    (D : FiniteEnsemble α) (n : ℕ) :
    ∑ x ∈ D.support n, D.mass n x = 1 := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  let := D.seedNonempty n
  have hmaps :
      ((Finset.univ : Finset (D.Seed n)) : Set (D.Seed n)).MapsTo
        (D.sample n) (D.support n) := by
    intro seed _
    simp [support]
  have hpartition := uniformProbability_eq_sum_fiberwise_internal
    (Finset.univ : Finset (D.Seed n)) (D.support n) (D.sample n) hmaps
  rw [uniformProbability_univ_internal] at hpartition
  simpa [mass, probability, event] using hpartition.symm

theorem probability_product_internal (D : FiniteEnsemble α)
    (E : FiniteEnsemble β) (n : ℕ) (P : α → Prop) (Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (D.product E).probability n (fun xy => P xy.1 ∧ Q xy.2) =
      D.probability n P * E.probability n Q := by
  let := D.seedFintype n
  let := D.seedDecidableEq n
  let := E.seedFintype n
  let := E.seedDecidableEq n
  simp only [product, probability, event]
  exact uniformProbability_product_internal
    (fun seed : D.Seed n => P (D.sample n seed))
    (fun seed : E.Seed n => Q (E.sample n seed))

theorem probability_dirac_internal (x : ℕ → α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    (dirac x).probability n P = if P (x n) then 1 else 0 := by
  let := (dirac x).seedFintype n
  let := (dirac x).seedDecidableEq n
  let := (dirac x).seedNonempty n
  by_cases hP : P (x n)
  · rw [ite_eq_left hP]
    unfold probability
    rw [show (dirac x).event n P = Finset.univ by
      ext seed
      simp [event, dirac, hP]]
    exact uniformProbability_univ_internal
  · rw [ite_eq_right hP]
    unfold probability
    rw [show (dirac x).event n P = ∅ by
      ext seed
      simp [event, dirac, hP]
      rfl]
    exact uniformProbability_empty_internal

end FiniteEnsemble

namespace DyadicEnsemble

variable {α : Type u}

theorem probability_toFinite_internal (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.toFinite.probability n P = D.probability n P := by
  change
    ((Finset.univ.filter fun seed : Fin (D.seedLength n) → Bool =>
        P (D.sample n seed)).card : ℚ) /
        Fintype.card (Fin (D.seedLength n) → Bool) =
      ((Finset.univ.filter fun seed : Fin (D.seedLength n) → Bool =>
        P (D.sample n seed)).card : ℚ) / 2 ^ D.seedLength n
  rw [card_finArrowBool]
  norm_cast

end DyadicEnsemble

end Complexity
