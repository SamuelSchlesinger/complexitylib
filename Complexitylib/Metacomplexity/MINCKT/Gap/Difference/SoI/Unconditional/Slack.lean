/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack.Internal

/-!
# Explicit slack amplification for the conditional MinKT reduction

The final clock is enlarged constructively so that its base-two logarithm pays
the paired-estimator loss, the condition-estimator loss, the SoI loss, and the
fixed pair compiler overhead. This removes the two abstract `LossBudget`
inequalities from the exact two-query reduction.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

/-- The slack-amplified clock dominates the source time. -/
theorem finalClock_source_le
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    time ≤ finalClock clock additive compilerLoss
      outputLength conditionLength time :=
  finalClock_source_le_internal clock additive compilerLoss
    outputLength conditionLength time

/-- The slack-amplified clock dominates the fourfold query clock. -/
theorem finalClock_iterateFour_le
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    clockIterate clock 4 (totalTime outputLength conditionLength time) ≤
      finalClock clock additive compilerLoss
        outputLength conditionLength time :=
  finalClock_iterateFour_le_internal clock additive compilerLoss
    outputLength conditionLength time

/-- The final logarithmic slack contains its complete explicit loss
exponent. -/
theorem slackExponent_le_log_finalClock
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    slackExponent clock additive compilerLoss
        outputLength conditionLength time ≤
      Nat.log 2 (finalClock clock additive compilerLoss
        outputLength conditionLength time) :=
  slackExponent_le_log_finalClock_internal clock additive compilerLoss
    outputLength conditionLength time

/-- Monotonicity moves all three query losses from `t'` to the total source
parameter, after which the amplified final slack pays them. -/
theorem lowerLoss_budget
    {clock : ℕ → ℕ} (hclock : Monotone clock)
    (additive compilerLoss : ℕ) (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).pairInput inst) +
          logarithmicSoILoss clock additive
            ((plan clock compilerLoss).soiTime inst) +
        (plan clock compilerLoss).correction inst ≤
      (parameters clock additive compilerLoss).logarithmicSlack inst :=
  lowerLoss_budget_internal hclock additive compilerLoss inst

/-- The constructive correction exactly pays the condition-query and compiler
losses. -/
theorem upperLoss_budget
    (clock : ℕ → ℕ) (compilerLoss : ℕ)
    (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).conditionInput inst) +
        (plan clock compilerLoss).pairUpperLoss inst ≤
      (plan clock compilerLoss).correction inst :=
  upperLoss_budget_internal clock compilerLoss inst

/-- Slack amplification and the paired upper-chain theorem produce the full
compatibility contract with no remaining clock or loss hypotheses. -/
theorem IsRegularClock.compatible
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
        (logarithmicSoILoss clock additive) :=
  Slack.IsRegularClock.compatible_internal hclock hpair

/-- The operational condition-first compiler closes the last machine-specific
premise of the slack-amplified schedule. -/
theorem IsRegularClock.compatible_of_pairComposition
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
  Slack.IsRegularClock.compatible_of_pairComposition_internal hclock hsupports

/-- Estimator correctness on the plan's queries forces the clock to leave room
to print the paired output. For `x = 1^n`, `y = []`, and `t = 0`, the paired
query asks for `pair x y`, of length `2n + 2`, and the upper half of the
sandwich needs a program printing it within the transformed clock `p(p(n))`;
a run of `s` steps prints at most `s` output bits. -/
theorem two_mul_add_two_le_clock_clock_of_satisfiesBoundsOn
    {tapes : ℕ} {machine : TM tapes} {clock : ℕ → ℕ} {compilerLoss : ℕ}
    {estimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : estimate.SatisfiesBoundsOn machine (ordinaryParameters clock)
      (plan clock compilerLoss).IsEstimatorQuery) (length : ℕ) :
    2 * length + 2 ≤ clock (clock length) :=
  two_mul_add_two_le_clock_clock_of_satisfiesBoundsOn_internal hestimate length

/-- Finite ordinary complexity on every plan query forces `2n + 2 ≤ p(n)`: the
paired query for `x = 1^n`, `y = []`, and `t = 0` asks for `pair x y`, of
length `2n + 2`, within its source clock `p(n)`. -/
theorem two_mul_add_two_le_clock_of_forall_ne_top
    {tapes : ℕ} {machine : TM tapes} {clock : ℕ → ℕ} {compilerLoss : ℕ}
    (hfinite : ∀ query : MINKT.Instance,
      (plan clock compilerLoss).IsEstimatorQuery query →
      machine.timeBoundedKolmogorovComplexity query.output query.time ≠ ⊤)
    (length : ℕ) :
    2 * length + 2 ≤ clock length :=
  two_mul_add_two_le_clock_of_forall_ne_top_internal hfinite length

/-- At the admissible clock `id` (`isAdmissibleClock_id`), no estimator is
correct on the plan's queries, for any machine and compiler loss: the paired
query for `x = y = []` and `t = 0` asks for the two-bit output `pair [] []`
within zero steps. -/
theorem not_satisfiesBoundsOn_plan_id {tapes : ℕ} (machine : TM tapes)
    (compilerLoss : ℕ) (estimate : GapMINKT.Logarithmic.Estimator) :
    ¬ estimate.SatisfiesBoundsOn machine (ordinaryParameters id)
      (plan id compilerLoss).IsEstimatorQuery :=
  not_satisfiesBoundsOn_plan_id_internal machine compilerLoss estimate

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
