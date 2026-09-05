/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Rounds.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Counting.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Halving.Internal
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Rounds.Selection.Internal
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.GoodString
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Parameters.Internal
import Complexitylib.Metacomplexity.ScaledExponent

/-!
# Anti-Checker Lemma round parameters -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

theorem IsAccurateRoundEstimator.isAccurateRequiredRoundEstimator_internal
    {arity : ℕ} {beta : PositiveRationalScale}
    {target : BitString arity → Bool}
    {estimator : List (BitString arity) → BitString arity → ℕ}
    (hestimate : IsAccurateRoundEstimator beta target estimator) :
    IsAccurateRequiredRoundEstimator beta target estimator :=
  hestimate.approximatesRoundsUpTo_internal (requiredRoundCount beta arity)

theorem initialCandidateSurvivorCount_lt_two_pow_roundBlockCount_internal
    {arity : ℕ} (beta : PositiveRationalScale)
    (target : BitString arity → Bool) :
    AntiChecker.candidateSurvivorCount target
        (smallThreshold beta arity) [] <
      2 ^ roundBlockCount beta arity := by
  rw [AntiChecker.candidateSurvivorCount_nil_internal]
  calc
    (AntiChecker.candidateCodes arity
          (smallThreshold beta arity)).card ≤
        2 ^ (AntiChecker.codeLengthBound arity
          (smallThreshold beta arity) + 1) :=
      AntiChecker.card_candidateCodes_le_internal
        arity (smallThreshold beta arity)
    _ < 2 ^ (AntiChecker.codeLengthBound arity
          (smallThreshold beta arity) + 2) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    _ = 2 ^ roundBlockCount beta arity := rfl

theorem eventually_requiredRoundCount_le_sampleCount_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      requiredRoundCount beta arity ≤ sampleCount beta arity := by
  have harityBound :=
    PositiveRationalScale.eventually_coefficient_mul_succ_pow_le_powFloor
      beta 1 1
  have hconstantBound :=
    PositiveRationalScale.eventually_coefficient_mul_succ_pow_le_powFloor
      beta 52 0
  filter_upwards [harityBound, hconstantBound]
      with arity harityBound hconstantBound
  let hard := hardThreshold beta arity
  let small := smallThreshold beta arity
  have hhardPos : 0 < hard := by
    dsimp only [hard]
    exact PositiveRationalScale.powFloor_pos beta arity
  have harityLe : arity ≤ hard := by
    change arity ≤ beta.powFloor arity
    have : arity + 1 ≤ beta.powFloor arity := by
      simpa using harityBound
    omega
  have hconstantLe : 52 ≤ hard := by
    change 52 ≤ beta.powFloor arity
    simpa using hconstantBound
  have hsmallLe : small ≤ hard := by
    dsimp only [small, hard]
    exact smallThreshold_le_hardThreshold_internal beta arity
  have hinterior :
      2 * (arity + small) + 6 ≤ 4 * hard + 6 := by
    omega
  have hblockBound :
      AntiChecker.codeLengthBound arity small + 2 ≤
        13 * hard ^ 2 := by
    unfold AntiChecker.codeLengthBound
    calc
      1 + small * (2 * (arity + small) + 6) + 2 ≤
          1 + hard * (4 * hard + 6) + 2 :=
        Nat.add_le_add_right
          (Nat.add_le_add_left
            (Nat.mul_le_mul hsmallLe hinterior) 1) 2
      _ ≤ 13 * hard ^ 2 := by
        nlinarith
  have hrequiredLe : requiredRoundCount beta arity ≤ hard ^ 4 := by
    unfold requiredRoundCount roundShrinkDenominator roundBlockCount
    dsimp only [small] at hblockBound
    calc
      4 * arity *
            (AntiChecker.codeLengthBound arity
              (smallThreshold beta arity) + 2) ≤
          4 * hard * (13 * hard ^ 2) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_left 4 harityLe) hblockBound
      _ = 52 * hard ^ 3 := by ring
      _ ≤ hard * hard ^ 3 :=
        Nat.mul_le_mul_right (hard ^ 3) hconstantLe
      _ = hard ^ 4 := by ring
  calc
    requiredRoundCount beta arity ≤ hard ^ 4 := hrequiredLe
    _ ≤ beta.powFloor (4 * arity) := by
      dsimp only [hard]
      exact PositiveRationalScale.powFloor_pow_le_mul beta arity 4
    _ ≤ beta.powFloor (fixedConstant * arity) :=
      PositiveRationalScale.powFloor_mono beta (by
        unfold fixedConstant
        omega)
    _ = sampleCount beta arity := rfl

theorem eventually_exists_shrinkTrace_of_isHardAt_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (target : BitString arity → Bool)
          (estimator :
            List (BitString arity) → BitString arity → ℕ),
        IsHardAt beta target →
          IsAccurateRoundEstimator beta target estimator →
            ∀ rounds,
              ∃ inputs : List (BitString arity),
                inputs.length = rounds ∧
                  AntiChecker.IsShrinkTrace
                    (roundShrinkDenominator arity) target
                    (smallThreshold beta arity) inputs := by
  filter_upwards
      [eventually_hasShrinkExtension_of_isHardAt beta,
        Filter.eventually_ge_atTop 1]
      with arity hgood harity
  intro target estimator hhard hestimate rounds
  have htrace :=
    AntiChecker.exists_isShrinkTrace_length_of_approximatesEveryRound_internal
      (precision := roundPrecision arity) (denominator := 2 * arity)
      estimator rounds (by unfold roundPrecision; omega) (by omega)
      (by unfold roundPrecision; omega) hestimate
      (fun inputs => hgood target inputs hhard)
  simpa [roundShrinkDenominator, ← Nat.mul_assoc] using htrace

theorem eventually_exists_requiredShrinkTrace_of_isHardAt_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (target : BitString arity → Bool)
          (estimator :
            List (BitString arity) → BitString arity → ℕ),
        IsHardAt beta target →
          IsAccurateRequiredRoundEstimator beta target estimator →
            ∃ inputs : List (BitString arity),
              inputs.length = requiredRoundCount beta arity ∧
                AntiChecker.IsShrinkTrace
                  (roundShrinkDenominator arity) target
                  (smallThreshold beta arity) inputs := by
  filter_upwards
      [eventually_hasShrinkExtension_of_isHardAt beta,
        Filter.eventually_ge_atTop 1]
      with arity hgood harity
  intro target estimator hhard hestimate
  have htrace :=
    AntiChecker.exists_isShrinkTrace_length_of_approximatesRoundsUpTo_internal
      (precision := roundPrecision arity) (denominator := 2 * arity)
      estimator (requiredRoundCount beta arity)
      (by unfold roundPrecision; omega) (by omega)
      (by unfold roundPrecision; omega) hestimate
      (fun inputs => hgood target inputs hhard)
  simpa [roundShrinkDenominator, ← Nat.mul_assoc] using htrace

theorem eventually_padInputsTo_isFor_of_isEstimateSelectionTrace_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (target : BitString arity → Bool)
          (estimator :
            List (BitString arity) → BitString arity → ℕ)
          (inputs : List (BitString arity)),
        IsHardAt beta target →
          IsAccurateRequiredRoundEstimator beta target estimator →
            inputs.length = requiredRoundCount beta arity →
              AntiChecker.IsEstimateSelectionTrace estimator inputs →
                (AntiChecker.padInputsTo (sampleCount beta arity) inputs).length =
                    sampleCount beta arity ∧
                  AntiChecker.IsFor target (smallThreshold beta arity)
                    (AntiChecker.padInputsTo (sampleCount beta arity) inputs) := by
  filter_upwards
      [eventually_hasShrinkExtension_of_isHardAt beta,
        eventually_requiredRoundCount_le_sampleCount_internal beta]
      with arity hgood hbudget
  intro harity target estimator inputs hhard hestimate hlength hselection
  let : NeZero arity := ⟨harity⟩
  have hshrink' :=
    hselection.isShrinkTrace_of_length_le_internal
      (rounds := requiredRoundCount beta arity)
      (precision := roundPrecision arity) (denominator := 2 * arity)
      (by unfold roundPrecision; omega) (by omega)
      (by unfold roundPrecision; omega) hestimate
      (fun samplePrefix => hgood target samplePrefix hhard)
      (by rw [hlength])
  have hshrink :
      AntiChecker.IsShrinkTrace (roundShrinkDenominator arity) target
        (smallThreshold beta arity) inputs := by
    simpa [roundShrinkDenominator, ← Nat.mul_assoc] using hshrink'
  have hanti :
      AntiChecker.IsFor target (smallThreshold beta arity) inputs := by
    apply hshrink.isFor_of_initial_lt_two_pow_internal
      (blocks := roundBlockCount beta arity)
    · unfold roundShrinkDenominator
      omega
    · rw [hlength]
      rfl
    · exact
        initialCandidateSurvivorCount_lt_two_pow_roundBlockCount_internal
          beta target
  have hlengthLe : inputs.length ≤ sampleCount beta arity := by
    rw [hlength]
    exact hbudget
  exact ⟨AntiChecker.length_padInputsTo_internal hlengthLe,
    hanti.padInputsTo_internal⟩

theorem eventually_exists_isFor_length_eq_sampleCount_of_isHardAt_internal
    (beta : PositiveRationalScale) :
    ∀ᶠ arity : ℕ in Filter.atTop,
      ∀ (harity : arity ≠ 0),
        letI : NeZero arity := ⟨harity⟩
        ∀ (target : BitString arity → Bool)
          (estimator :
            List (BitString arity) → BitString arity → ℕ),
        IsHardAt beta target →
          IsAccurateRequiredRoundEstimator beta target estimator →
            ∃ inputs : List (BitString arity),
              inputs.length = sampleCount beta arity ∧
                AntiChecker.IsFor target (smallThreshold beta arity) inputs := by
  filter_upwards
      [eventually_exists_requiredShrinkTrace_of_isHardAt_internal beta,
        eventually_requiredRoundCount_le_sampleCount_internal beta]
      with arity htrace hbudget
  intro harity target estimator hhard hestimate
  let : NeZero arity := ⟨harity⟩
  obtain ⟨inputs, hlength, hshrink⟩ :=
    htrace target estimator hhard hestimate
  have hanti :
      AntiChecker.IsFor target (smallThreshold beta arity) inputs := by
    apply hshrink.isFor_of_initial_lt_two_pow_internal
      (blocks := roundBlockCount beta arity)
    · unfold roundShrinkDenominator
      omega
    · rw [hlength]
      rfl
    · exact
        initialCandidateSurvivorCount_lt_two_pow_roundBlockCount_internal
          beta target
  have hlengthLe : inputs.length ≤ sampleCount beta arity :=
    hlength.le.trans hbudget
  refine ⟨AntiChecker.padInputsTo (sampleCount beta arity) inputs,
    AntiChecker.length_padInputsTo_internal hlengthLe, ?_⟩
  exact hanti.padInputsTo_internal

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
