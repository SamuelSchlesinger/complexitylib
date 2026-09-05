/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Internal

/-!
# Explicit slack amplification -- proof internals
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

theorem paddedTime_le_totalTime_internal (inst : MINCKT.Instance) :
    paddedTime inst ≤
      totalTime inst.output.length inst.condition.length inst.time := by
  exact paddedTime_le_total_internal inst

theorem finalClock_source_le_internal
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    time ≤ finalClock clock additive compilerLoss
      outputLength conditionLength time := by
  let total := totalTime outputLength conditionLength time
  let exponent := slackExponent clock additive compilerLoss
    outputLength conditionLength time
  have htime : time ≤ total + 1 := by
    dsimp [total, totalTime]
    omega
  have hright : total + 1 ≤
      (clockIterate clock 4 total + 1) * (total + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hpow : 0 < 2 ^ exponent := Nat.pow_pos (by omega)
  exact htime.trans <| hright.trans <|
    Nat.le_mul_of_pos_left _ hpow

theorem finalClock_iterateFour_le_internal
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    clockIterate clock 4 (totalTime outputLength conditionLength time) ≤
      finalClock clock additive compilerLoss
        outputLength conditionLength time := by
  let total := totalTime outputLength conditionLength time
  let exponent := slackExponent clock additive compilerLoss
    outputLength conditionLength time
  have hright : clockIterate clock 4 total ≤
      (clockIterate clock 4 total + 1) * (total + 1) := by
    exact (Nat.le_add_right _ 1).trans <|
      Nat.le_mul_of_pos_right _ (by omega)
  have hpow : 0 < 2 ^ exponent := Nat.pow_pos (by omega)
  exact hright.trans (Nat.le_mul_of_pos_left _ hpow)

theorem slackExponent_le_log_finalClock_internal
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    slackExponent clock additive compilerLoss
        outputLength conditionLength time ≤
      Nat.log 2 (finalClock clock additive compilerLoss
        outputLength conditionLength time) := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  apply Nat.le_mul_of_pos_right
  exact Nat.mul_pos (by omega) (by omega)

theorem losses_le_slackExponent_internal
    {clock : ℕ → ℕ} (hclock : Monotone clock)
    (additive compilerLoss : ℕ) (inst : MINCKT.Instance) :
    Nat.log 2 (clockIterate clock 2 (paddedTime inst)) +
          logarithmicSoILoss clock additive
            (clockIterate clock 2 (paddedTime inst)) +
        correction clock compilerLoss inst ≤
      slackExponent clock additive compilerLoss inst.output.length
        inst.condition.length inst.time := by
  have htotal := paddedTime_le_totalTime_internal inst
  have htwo :
      Nat.log 2 (clockIterate clock 2 (paddedTime inst)) ≤
        Nat.log 2 (clockIterate clock 2
          (totalTime inst.output.length inst.condition.length inst.time) + 1) :=
    Nat.log_mono_right <|
      (clockIterate_monotone_internal hclock 2 htotal).trans
        (Nat.le_add_right _ 1)
  have hthree :
      Nat.log 2 (clockIterate clock 3 (paddedTime inst)) ≤
        Nat.log 2 (clockIterate clock 3
          (totalTime inst.output.length inst.condition.length inst.time) + 1) :=
    Nat.log_mono_right <|
      (clockIterate_monotone_internal hclock 3 htotal).trans
        (Nat.le_add_right _ 1)
  have hfour :
      Nat.log 2 (clockIterate clock 4 (paddedTime inst)) ≤
        Nat.log 2 (clockIterate clock 4
          (totalTime inst.output.length inst.condition.length inst.time) + 1) :=
    Nat.log_mono_right <|
      (clockIterate_monotone_internal hclock 4 htotal).trans
        (Nat.le_add_right _ 1)
  simp only [clockIterate] at htwo
  simp only [clockIterate] at hthree
  simp only [clockIterate] at hfour
  simp only [logarithmicSoILoss, correction, slackExponent, clockIterate]
  omega

theorem upperLoss_budget_internal
    (clock : ℕ → ℕ) (compilerLoss : ℕ)
    (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).conditionInput inst) +
        (plan clock compilerLoss).pairUpperLoss inst ≤
      (plan clock compilerLoss).correction inst := by
  simp [plan, Iterated.plan, correction, Plan.conditionInput,
    ordinaryParameters, GapMINKT.Logarithmic.Parameters.logarithmicSlack,
    GapMINKT.Logarithmic.Parameters.transformedTime, clockIterate]

theorem lowerLoss_budget_internal
    {clock : ℕ → ℕ} (hclock : Monotone clock)
    (additive compilerLoss : ℕ) (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).pairInput inst) +
          logarithmicSoILoss clock additive
            ((plan clock compilerLoss).soiTime inst) +
        (plan clock compilerLoss).correction inst ≤
      (parameters clock additive compilerLoss).logarithmicSlack inst := by
  have hloss := losses_le_slackExponent_internal hclock additive compilerLoss inst
  have hslack := slackExponent_le_log_finalClock_internal clock additive
    compilerLoss inst.output.length inst.condition.length inst.time
  have h := hloss.trans hslack
  simp only [plan, Iterated.plan, Plan.pairInput, ordinaryParameters,
    GapMINKT.Logarithmic.Parameters.logarithmicSlack,
    GapMINKT.Logarithmic.Parameters.transformedTime] at h ⊢
  exact h

theorem IsRegularClock.compatible_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} {additive compilerLoss : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hpair : ∀ inst,
      ordinaryMachine.timeBoundedKolmogorovComplexity
            (pair inst.output inst.condition)
              ((plan clock compilerLoss).pairInputTime inst) ≤
        inst.complexity conditionalMachine +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              inst.condition inst.time +
          ((plan clock compilerLoss).pairUpperLoss inst : WithTop ℕ)) :
    Compatible (plan clock compilerLoss) ordinaryMachine conditionalMachine
      (ordinaryParameters clock) (parameters clock additive compilerLoss) clock
        (logarithmicSoILoss clock additive) := by
  constructor
  · intro inst
    have hthreeFour : clockIterate clock 3 (paddedTime inst) ≤
        clockIterate clock 4 (paddedTime inst) := hclock.dominates _
    have hfourTotal := clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_totalTime_internal inst)
    exact (hthreeFour.trans hfourTotal).trans <|
      finalClock_iterateFour_le_internal clock additive compilerLoss
        inst.output.length inst.condition.length inst.time
  · intro inst
    exact (paddedTime_size_le_internal inst).trans
      (clockIterate_dominates_internal hclock.dominates 2 _)
  · intro inst
    rfl
  · intro inst
    exact (clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_totalTime_internal inst)).trans <|
        finalClock_iterateFour_le_internal clock additive compilerLoss
          inst.output.length inst.condition.length inst.time
  · intro inst
    rfl
  · exact hpair
  · exact upperLoss_budget_internal clock compilerLoss
  · exact lowerLoss_budget_internal hclock.monotone additive compilerLoss

theorem IsRegularClock.compatible_of_pairComposition_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} {additive compilerLoss : ℕ}
    {composition : PairCompositionPlan}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine) :
    Compatible (plan clock compilerLoss) ordinaryMachine conditionalMachine
      (ordinaryParameters clock) (parameters clock additive compilerLoss) clock
        (logarithmicSoILoss clock additive) :=
  Slack.IsRegularClock.compatible_internal hclock
    hsupports.pair_upper_internal

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
