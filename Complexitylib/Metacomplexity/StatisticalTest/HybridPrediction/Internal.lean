/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.StatisticalTest.HybridPrediction.Defs
import Complexitylib.Classes.AverageCase.FiniteEnsemble
import Complexitylib.Metacomplexity.StatisticalTest.Prediction.Internal

/-!
# Splitting one hybrid coordinate into a next-bit experiment -- proof internals
-/


public section

namespace Complexity

namespace BitGenerator

private def splitCandidate {seedLength outputLength : ℕ}
    (step : Fin outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    CandidateBackground seedLength outputLength step × Bool :=
  let tail := blockSnd seedLength outputLength randomness
  ((blockFst seedLength outputLength randomness,
      ⟨Function.update tail step false, by simp⟩), tail step)

private theorem splitCandidate_assembleCandidate
    {seedLength outputLength : ℕ} {step : Fin outputLength}
    (sample : CandidateBackground seedLength outputLength step × Bool) :
    splitCandidate step (assembleCandidate sample.1 sample.2) = sample := by
  rcases sample with ⟨⟨seed, tail⟩, candidate⟩
  simp only [splitCandidate, assembleCandidate, blockFst_append,
    blockSnd_append, Function.update_self, Prod.mk.injEq, true_and]
  constructor
  · apply Subtype.ext
    change Function.update (Function.update tail.val step candidate)
      step false = tail.val
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr tail.property.symm
  · trivial

private theorem assembleCandidate_splitCandidate
    {seedLength outputLength : ℕ} (step : Fin outputLength)
    (randomness : Fin (seedLength + outputLength) → Bool) :
    assembleCandidate (splitCandidate step randomness).1
      (splitCandidate step randomness).2 = randomness := by
  simp only [splitCandidate, assembleCandidate]
  rw [Function.update_idem, Function.update_eq_self,
    blockAppend_fst_snd]

private def candidateEquiv {seedLength outputLength : ℕ}
    (step : Fin outputLength) :
    (CandidateBackground seedLength outputLength step × Bool) ≃
      (Fin (seedLength + outputLength) → Bool) where
  toFun sample := assembleCandidate sample.1 sample.2
  invFun := splitCandidate step
  left_inv := splitCandidate_assembleCandidate
  right_inv := assembleCandidate_splitCandidate step

private theorem uniformProbability_finArrowBool
    {length : ℕ} (event : Finset (Fin length → Bool)) :
    uniformProbability event = eventProb event := by
  simp [uniformProbability, eventProb]

private theorem blockAppend_natAdd
    {seedLength outputLength : ℕ}
    (seed : Fin seedLength → Bool) (tail : Fin outputLength → Bool)
    (coordinate : Fin outputLength) :
    blockAppend seedLength outputLength seed tail
        (Fin.natAdd seedLength coordinate) = tail coordinate := by
  have happ := congrFun
    (blockSnd_append seedLength outputLength seed tail) coordinate
  rw [blockSnd_apply] at happ
  exact happ

private theorem hybridOutput_targetCandidate_eq_next
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (step : Fin outputLength)
    (background : CandidateBackground seedLength outputLength step)
    (candidate : Bool) :
    generator.hybridOutput step.val
        (assembleCandidate background (generator.targetBit step background)) =
      generator.hybridOutput (step.val + 1)
        (assembleCandidate background candidate) := by
  funext coordinate
  by_cases hbefore : coordinate.val < step.val
  · have hbeforeNext : coordinate.val < step.val + 1 := by omega
    simp [hybridOutput, hbefore, hbeforeNext, assembleCandidate]
  · by_cases hequal : coordinate = step
    · subst coordinate
      simp [hybridOutput, assembleCandidate, targetBit,
        blockAppend_natAdd]
    · have hafter : step.val < coordinate.val := by omega
      have hnotNext : ¬coordinate.val < step.val + 1 := by omega
      simp [hybridOutput, hbefore, hnotNext, assembleCandidate, hequal,
        blockAppend_natAdd]

theorem candidateAcceptanceProbability_eq_hybrid_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool))
    (step : Fin outputLength) :
    NextBitPrediction.candidateAcceptanceProbability
        (generator.testAtCandidate test step) =
      generator.hybridAcceptanceProbability test step.val := by
  classical
  have htransport := uniformProbability_equiv (candidateEquiv step)
    (fun randomness => generator.hybridOutput step.val randomness ∈ test)
  rw [uniformProbability_finArrowBool] at htransport
  simp [NextBitPrediction.candidateAcceptanceProbability, testAtCandidate,
    hybridAcceptanceProbability, hybridAcceptedRandomness]
  exact htransport

theorem targetAcceptanceProbability_eq_nextHybrid_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool))
    (step : Fin outputLength) :
    NextBitPrediction.targetAcceptanceProbability
        (generator.targetBit step) (generator.testAtCandidate test step) =
      generator.hybridAcceptanceProbability test (step.val + 1) := by
  classical
  unfold NextBitPrediction.targetAcceptanceProbability
  simp only [testAtCandidate, decide_eq_true_eq]
  let P : CandidateBackground seedLength outputLength step → Prop :=
    fun background =>
      generator.hybridOutput step.val
        (assembleCandidate background (generator.targetBit step background)) ∈
          test
  change uniformProbability (Finset.univ.filter P) = _
  have hproduct := uniformProbability_product P (fun _candidate : Bool => True)
  have hduplicate :
      uniformProbability (Finset.univ.filter P) =
        uniformProbability (Finset.univ.filter fun sample :
          CandidateBackground seedLength outputLength step × Bool =>
            P sample.1 ∧ True) := by
    have h := hproduct.symm
    simp only [and_true, Finset.filter_true, uniformProbability_univ,
      mul_one] at h ⊢
    exact h
  rw [hduplicate]
  have htransport := uniformProbability_equiv (candidateEquiv step)
    (fun randomness =>
      generator.hybridOutput (step.val + 1) randomness ∈ test)
  rw [uniformProbability_finArrowBool] at htransport
  calc
    uniformProbability (Finset.univ.filter fun sample :
        CandidateBackground seedLength outputLength step × Bool =>
          P sample.1 ∧ True) =
        uniformProbability (Finset.univ.filter fun sample :
          CandidateBackground seedLength outputLength step × Bool =>
            generator.hybridOutput (step.val + 1)
              (candidateEquiv step sample) ∈ test) := by
      apply congrArg uniformProbability
      ext sample
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      change P sample.1 ↔
        generator.hybridOutput (step.val + 1)
          (assembleCandidate sample.1 sample.2) ∈ test
      unfold P
      rw [hybridOutput_targetCandidate_eq_next
        generator step sample.1 sample.2]
    _ = eventProb (Finset.univ.filter fun randomness :
          Fin (seedLength + outputLength) → Bool =>
            generator.hybridOutput (step.val + 1) randomness ∈ test) :=
      htransport
    _ = generator.hybridAcceptanceProbability test (step.val + 1) := by
      rfl

theorem predictionSuccessProbability_eq_half_add_hybridGap_internal
    {seedLength outputLength : ℕ}
    (generator : BitGenerator seedLength outputLength)
    (test : Finset (Fin outputLength → Bool))
    (step : Fin outputLength) :
    NextBitPrediction.successProbability
        (generator.targetBit step) (generator.testAtCandidate test step) =
      1 / 2 + generator.hybridGap test step.val := by
  rw [NextBitPrediction.successProbability_eq_half_add_gap_internal,
    targetAcceptanceProbability_eq_nextHybrid_internal,
    candidateAcceptanceProbability_eq_hybrid_internal]
  unfold hybridGap
  ring

end BitGenerator

end Complexity
