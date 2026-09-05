/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.GlobalSampling.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal
import Complexitylib.Metacomplexity.BooleanDependency.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Averaging.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.Internal
import Complexitylib.Metacomplexity.NisanWigderson.Reconstruction.RepeatedSampling.Internal
import Complexitylib.Metacomplexity.StatisticalTest.Hybrid.Internal
import Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Internal
import Complexitylib.Metacomplexity.StatisticalTest.Internal

/-!
# Globally sampling NW reconstruction coordinates and advice -- proof internals
-/


public section

namespace Complexity

namespace NWDesign

private def rawReconstructionAdviceEquiv
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength) :
    RawReconstructionAdvice outputLength seedLength ≃
      design.ReconstructionAdvice current ×
        (((design.outsideCoordinates current)ᶜ : Finset (Fin seedLength)) → Bool) ×
          (((laterCoordinates current)ᶜ : Finset (Fin outputLength)) → Bool) where
  toFun raw :=
    let seedParts := BooleanDependency.assignmentSplitEquiv
      (design.outsideCoordinates current) raw.1
    let tailParts := BooleanDependency.assignmentSplitEquiv
      (laterCoordinates current) raw.2.1
    ((seedParts.1, (tailParts.1, raw.2.2)),
      (seedParts.2, tailParts.2))
  invFun sample :=
    let advice := sample.1
    let ignored := sample.2
    ((BooleanDependency.assignmentSplitEquiv
        (design.outsideCoordinates current)).symm
        (advice.1, ignored.1),
      ((BooleanDependency.assignmentSplitEquiv
        (laterCoordinates current)).symm
        (advice.2.1, ignored.2), advice.2.2))
  left_inv raw := by
    rcases raw with ⟨seed, tail, candidate⟩
    simp
  right_inv sample := by
    rcases sample with ⟨⟨outside, later, candidate⟩, ignoredSeed, ignoredTail⟩
    simp

private theorem rawReconstructionAdviceEquiv_fst
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (current : Fin outputLength)
    (raw : RawReconstructionAdvice outputLength seedLength) :
    (rawReconstructionAdviceEquiv design current raw).1 =
      design.reconstructionAdviceOfRaw current raw := by
  rfl

theorem goodRawAdviceProbability_eq_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (current : Fin outputLength) (agreementThreshold : ℚ) :
    uniformProbability (Finset.univ.filter fun raw :
        RawReconstructionAdvice outputLength seedLength =>
      agreementThreshold ≤
        design.reconstructionAgreementProbability hardFunction test current
          (design.reconstructionAdviceOfRaw current raw)) =
      design.goodReconstructionAdviceProbability hardFunction test current
        agreementThreshold := by
  let good : design.ReconstructionAdvice current → Prop :=
    fun advice => agreementThreshold ≤
      design.reconstructionAgreementProbability hardFunction test current advice
  let ignored :=
    (((design.outsideCoordinates current)ᶜ : Finset (Fin seedLength)) → Bool) ×
      (((laterCoordinates current)ᶜ : Finset (Fin outputLength)) → Bool)
  have htransport := uniformProbability_equiv_internal
    (rawReconstructionAdviceEquiv design current)
    (fun sample : design.ReconstructionAdvice current × ignored =>
      good sample.1)
  have hproduct := uniformProbability_product_internal good
    (fun _sample : ignored => True)
  have hproduct' :
      uniformProbability (Finset.univ.filter fun sample :
          design.ReconstructionAdvice current × ignored => good sample.1) =
        uniformProbability (Finset.univ.filter good) := by
    simpa [uniformProbability_univ_internal] using hproduct
  simpa [good, goodReconstructionAdviceProbability,
    rawReconstructionAdviceEquiv_fst] using htransport.trans hproduct'

theorem goodReconstructionTrialProbability_eq_average_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) (houtputLength : 0 < outputLength) :
    design.goodReconstructionTrialProbability hardFunction test
        agreementThreshold =
      (∑ current : Fin outputLength,
        design.goodReconstructionAdviceProbability hardFunction test current
          agreementThreshold) / outputLength := by
  let : Nonempty (Fin outputLength) := ⟨⟨0, houtputLength⟩⟩
  let event := fun current (raw :
      RawReconstructionAdvice outputLength seedLength) =>
    agreementThreshold ≤
      design.reconstructionAgreementProbability hardFunction test current
        (design.reconstructionAdviceOfRaw current raw)
  have haverage := uniformProbability_product_eq_average_fibers_internal event
  have hconditional : ∀ current,
      uniformProbability (Finset.univ.filter (event current)) =
        design.goodReconstructionAdviceProbability hardFunction test current
          agreementThreshold := by
    intro current
    exact goodRawAdviceProbability_eq_internal
      design hardFunction test current agreementThreshold
  simp only [goodReconstructionTrialProbability, goodReconstructionTrialEvent,
    reconstructionTrialAgreementProbability, reconstructionAdviceOfTrial,
    event, hconditional, Fintype.card_fin] at haverage ⊢
  exact haverage

theorem exists_orientation_sum_averageReconstructionAgreement_ge_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool)) (advantage : ℚ)
    (hadvantage : advantage ≤
      (design.generator hardFunction).distinguishingAdvantage test) :
    ∃ complement : Bool,
      (outputLength : ℚ) / 2 + advantage ≤
        ∑ current : Fin outputLength,
          design.averageReconstructionAgreement hardFunction
            (BitGenerator.orientTest test complement) current := by
  obtain ⟨complement, horiented⟩ :=
    BitGenerator.exists_orientation_of_distinguishingAdvantage_internal
      (design.generator hardFunction) test hadvantage
  refine ⟨complement, ?_⟩
  have hgap : advantage ≤
      ∑ current : Fin outputLength,
        (design.generator hardFunction).hybridGap
          (BitGenerator.orientTest test complement) current.val := by
    rw [Fin.sum_univ_eq_sum_range,
      BitGenerator.sum_hybridGap_internal]
    exact horiented
  have hagreement : ∀ current : Fin outputLength,
      design.averageReconstructionAgreement hardFunction
          (BitGenerator.orientTest test complement) current =
        1 / 2 + (design.generator hardFunction).hybridGap
          (BitGenerator.orientTest test complement) current.val := by
    intro current
    rw [← BitGenerator.predictionSuccessProbability_eq_half_add_hybridGap_internal,
      predictionSuccessProbability_eq_averageReconstructionAgreement_internal]
  simp_rw [hagreement, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  nlinarith

theorem exists_orientation_goodReconstructionTrialProbability_ge_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool)) (density : ℚ)
    (houtputLength : 0 < outputLength) (hdensity : 0 ≤ density)
    (hdensityLeOne : density ≤ 1)
    (hadvantage : density ≤
      (design.generator hardFunction).distinguishingAdvantage test) :
    ∃ complement : Bool,
      (density / (outputLength : ℚ)) / 2 ≤
        design.goodReconstructionTrialProbability hardFunction
          (BitGenerator.orientTest test complement)
          (1 / 2 + (density / (outputLength : ℚ)) / 2) := by
  obtain ⟨complement, hsumLower⟩ :=
    exists_orientation_sum_averageReconstructionAgreement_ge_internal
      design hardFunction test density hadvantage
  refine ⟨complement, ?_⟩
  let agreementThreshold :=
    1 / 2 + (density / (outputLength : ℚ)) / 2
  let goodProbability := fun current : Fin outputLength =>
    design.goodReconstructionAdviceProbability hardFunction
      (BitGenerator.orientTest test complement) current agreementThreshold
  have hmeanUpper : ∀ current : Fin outputLength,
      design.averageReconstructionAgreement hardFunction
          (BitGenerator.orientTest test complement) current ≤
        agreementThreshold + goodProbability current *
          (1 - agreementThreshold) := by
    intro current
    rw [averageReconstructionAgreement_eq_uniformMean_internal]
    exact uniformMean_le_threshold_add_probability_internal
      (fun advice : design.ReconstructionAdvice current =>
        design.reconstructionAgreementProbability hardFunction
          (BitGenerator.orientTest test complement) current advice)
      agreementThreshold
      (fun _advice => uniformProbability_le_one_internal _)
  have hsumUpper :
      ∑ current : Fin outputLength,
          design.averageReconstructionAgreement hardFunction
            (BitGenerator.orientTest test complement) current ≤
        ∑ current : Fin outputLength,
          (agreementThreshold + goodProbability current *
            (1 - agreementThreshold)) := by
    exact Finset.sum_le_sum fun current _hcurrent => hmeanUpper current
  have hsumGoodNonneg :
      0 ≤ ∑ current : Fin outputLength, goodProbability current := by
    exact Finset.sum_nonneg fun current _hcurrent =>
      uniformProbability_nonneg_internal _
  have houtputLengthRat : 0 < (outputLength : ℚ) := by
    exact_mod_cast houtputLength
  have hdensityDivLeOne :
      density / (outputLength : ℚ) ≤ 1 := by
    have honeLe : (1 : ℚ) ≤ outputLength := by
      exact_mod_cast houtputLength
    calc
      density / (outputLength : ℚ) ≤ 1 / (outputLength : ℚ) := by
        gcongr
      _ ≤ 1 := by
        rw [div_le_iff₀ houtputLengthRat]
        simpa using honeLe
  have hthresholdNonneg : 0 ≤ agreementThreshold := by
    dsimp [agreementThreshold]
    positivity
  have hfactorNonneg : 0 ≤ 1 - agreementThreshold := by
    dsimp [agreementThreshold]
    linarith
  have hfactorLeOne : 1 - agreementThreshold ≤ 1 := by
    linarith
  have hproductLe :
      (∑ current : Fin outputLength, goodProbability current) *
          (1 - agreementThreshold) ≤
        ∑ current : Fin outputLength, goodProbability current := by
    exact mul_le_of_le_one_right hsumGoodNonneg hfactorLeOne
  have hsumUpper' :
      ∑ current : Fin outputLength,
          design.averageReconstructionAgreement hardFunction
            (BitGenerator.orientTest test complement) current ≤
        (outputLength : ℚ) * agreementThreshold +
          (∑ current : Fin outputLength, goodProbability current) *
            (1 - agreementThreshold) := by
    calc
      _ ≤ ∑ current : Fin outputLength,
          (agreementThreshold + goodProbability current *
            (1 - agreementThreshold)) := hsumUpper
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp [nsmul_eq_mul]
  have hsumGoodLower :
      density / 2 ≤
        ∑ current : Fin outputLength, goodProbability current := by
    have hthresholdMul :
        (outputLength : ℚ) * agreementThreshold =
          (outputLength : ℚ) / 2 + density / 2 := by
      dsimp [agreementThreshold]
      field_simp [houtputLengthRat.ne']
    have hreplaceProduct :
        (outputLength : ℚ) * agreementThreshold +
            (∑ current : Fin outputLength, goodProbability current) *
              (1 - agreementThreshold) ≤
          (outputLength : ℚ) * agreementThreshold +
            ∑ current : Fin outputLength, goodProbability current :=
      add_le_add le_rfl hproductLe
    have hsumUpperSimple :
        ∑ current : Fin outputLength,
            design.averageReconstructionAgreement hardFunction
              (BitGenerator.orientTest test complement) current ≤
          (outputLength : ℚ) * agreementThreshold +
            ∑ current : Fin outputLength, goodProbability current :=
      hsumUpper'.trans hreplaceProduct
    rw [hthresholdMul] at hsumUpperSimple
    nlinarith
  rw [goodReconstructionTrialProbability_eq_average_internal
    design hardFunction (BitGenerator.orientTest test complement)
      agreementThreshold houtputLength]
  change (density / (outputLength : ℚ)) / 2 ≤
    (∑ current : Fin outputLength, goodProbability current) / outputLength
  rw [le_div_iff₀ houtputLengthRat]
  field_simp [houtputLengthRat.ne']
  nlinarith

theorem repeatedGoodReconstructionTrialProbability_eq_one_sub_pow_internal
    {outputLength inputLength seedLength : ℕ}
    (design : NWDesign outputLength inputLength seedLength)
    (hardFunction : (Fin inputLength → Bool) → Bool)
    (test : Finset (Fin outputLength → Bool))
    (agreementThreshold : ℚ) (trials : ℕ)
    (houtputLength : 0 < outputLength) :
    design.repeatedGoodReconstructionTrialProbability hardFunction test
        agreementThreshold trials =
      1 - (1 - design.goodReconstructionTrialProbability hardFunction test
        agreementThreshold) ^ trials := by
  let : Nonempty (ReconstructionTrial outputLength seedLength) :=
    ⟨(⟨0, houtputLength⟩, (fun _ => false), (fun _ => false), false)⟩
  exact uniformAtLeastOneProbability_eq_one_sub_pow_internal
    (design.goodReconstructionTrialEvent hardFunction test agreementThreshold)
    trials

theorem exists_goodReconstructionTrialProbability_ge_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 ≤ density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ complement : Bool,
      (density / (outputLength : ℚ)) / 2 ≤
          design.goodReconstructionTrialProbability hardFunction
            (BitGenerator.orientTest test complement)
            (1 / 2 + (density / (outputLength : ℚ)) / 2) ∧
        ∀ trial : ReconstructionTrial outputLength seedLength,
          design.reconstructionDataBitsAt trial.1 ≤
            budget + (seedLength - inputLength) + 1 := by
  have hdensityLeOne : density ≤ 1 :=
    hdense.trans (eventProb_le_one test)
  have hadvantage :=
    BitGenerator.density_le_distinguishingAdvantage_of_randomTest_internal
      hlow hrandom hdense
  obtain ⟨complement, hprobability⟩ :=
    exists_orientation_goodReconstructionTrialProbability_ge_internal
      design hardFunction test density houtputLength hdensity hdensityLeOne
      hadvantage
  exact ⟨complement, hprobability, fun trial =>
    reconstructionDataBitsAt_le_of_hasOverlapBudget_internal
      hbudget trial.1⟩

theorem exists_half_le_canonicalRepeatedGoodTrial_of_randomTest_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density)
    (hlow : (design.generator hardFunction).HasLowTimeBoundedComplexity
      machine time threshold)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ complement : Bool,
      1 / 2 ≤
          design.repeatedGoodReconstructionTrialProbability hardFunction
            (BitGenerator.orientTest test complement)
            (1 / 2 + (density / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength density) ∧
        ∀ trial : ReconstructionTrial outputLength seedLength,
          design.reconstructionDataBitsAt trial.1 ≤
            budget + (seedLength - inputLength) + 1 := by
  obtain ⟨complement, hsingle, hdata⟩ :=
    exists_goodReconstructionTrialProbability_ge_of_randomTest_internal
      houtputLength hdensity.le hlow hrandom hdense hbudget
  let : Nonempty (ReconstructionTrial outputLength seedLength) :=
    ⟨(⟨0, houtputLength⟩, (fun _ => false), (fun _ => false), false)⟩
  exact ⟨complement,
    half_le_uniformAtLeastOneProbability_of_singleDrawLower_internal
      (design.goodReconstructionTrialEvent hardFunction
        (BitGenerator.orientTest test complement)
        (1 / 2 + (density / (outputLength : ℚ)) / 2))
      (reconstructionAdviceTrialCount outputLength density)
      ((density / (outputLength : ℚ)) / 2) hsingle
      (one_le_reconstructionAdviceTrialCount_mul_halfAdvantage_internal
        outputLength density houtputLength hdensity),
    hdata⟩

theorem exists_half_le_canonicalRepeatedGoodTrial_of_seedDescriptions_internal
    {outputLength inputLength seedLength tapes time threshold budget : ℕ}
    {design : NWDesign outputLength inputLength seedLength}
    {hardFunction : (Fin inputLength → Bool) → Bool}
    {machine : TM tapes} {test : Finset (Fin outputLength → Bool)}
    {density : ℚ} (houtputLength : 0 < outputLength)
    (hdensity : 0 < density) (hseedLength : seedLength < threshold)
    (hproduces : ∀ seed,
      machine.ProducesInTime (List.ofFn seed)
        (List.ofFn (design.generator hardFunction seed)) time)
    (hrandom : BitGenerator.IsTimeBoundedRandomTest
      test machine time threshold)
    (hdense : BitGenerator.IsDenseTest test density)
    (hbudget : design.HasOverlapBudget budget) :
    ∃ complement : Bool,
      1 / 2 ≤
          design.repeatedGoodReconstructionTrialProbability hardFunction
            (BitGenerator.orientTest test complement)
            (1 / 2 + (density / (outputLength : ℚ)) / 2)
            (reconstructionAdviceTrialCount outputLength density) ∧
        ∀ trial : ReconstructionTrial outputLength seedLength,
          design.reconstructionDataBitsAt trial.1 ≤
            budget + (seedLength - inputLength) + 1 := by
  apply exists_half_le_canonicalRepeatedGoodTrial_of_randomTest_internal
    houtputLength hdensity (hrandom := hrandom) (hdense := hdense)
    (hbudget := hbudget)
  exact BitGenerator.hasLowTimeBoundedComplexity_of_seedDescriptions_internal
    hseedLength hproduces

end NWDesign

end Complexity
