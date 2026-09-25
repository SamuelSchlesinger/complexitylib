/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINKT.Gap.Logarithmic.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Chain.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Defs

/-!
# Building the conditional difference estimator from one ordinary estimator

This layer maps every conditional instance `(x,y,1^t)` to two ordinary MINKT
instances:

- the joint input `(pair x y, 1^a)`;
- the condition input `(y, 1^b)`.

One numerical estimator satisfying the unconditional Fact 3.4 sandwich is
evaluated on both. Their adjusted difference is the candidate conditional
estimator. `Compatible` exposes the remaining clock identities, upper-chain
bound, and loss budgets needed to instantiate `SatisfiesSoIInputs`.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

/-- Per-instance choices needed to form the two ordinary estimator queries. -/
structure Plan where
  /-- Source clock encoded in the paired-string estimator query. -/
  pairInputTime : MINCKT.Instance → ℕ
  /-- Source clock encoded in the condition-only estimator query. -/
  conditionInputTime : MINCKT.Instance → ℕ
  /-- Base time at which the SoI hypothesis is invoked. -/
  soiTime : MINCKT.Instance → ℕ
  /-- Additive loss of the paired upper-chain evaluator. -/
  pairUpperLoss : MINCKT.Instance → ℕ
  /-- Centering and rounding correction in the final difference. -/
  correction : MINCKT.Instance → ℕ

/-- Compiler and attained-minimum budgets for the paired upper-chain query. -/
structure PairCompositionPlan where
  /-- Compile a condition program and conditional result program into one
  ordinary program. -/
  compile : List Bool → List Bool → List Bool
  /-- Program-length budget for the condition minimum. -/
  conditionBound : MINCKT.Instance → ℕ
  /-- Program-length budget for the conditional result minimum. -/
  resultBound : MINCKT.Instance → ℕ

namespace Plan

/-- Ordinary MINKT query for the paired output. -/
def pairInput (plan : Plan) (inst : MINCKT.Instance) : MINKT.Instance where
  output := pair inst.output inst.condition
  time := plan.pairInputTime inst

/-- Ordinary MINKT query for the condition alone. -/
def conditionInput (plan : Plan) (inst : MINCKT.Instance) : MINKT.Instance where
  output := inst.condition
  time := plan.conditionInputTime inst

/-- Exactly the paired and condition-only MINKT queries issued by this plan. -/
def IsEstimatorQuery (plan : Plan) (query : MINKT.Instance) : Prop :=
  ∃ inst : MINCKT.Instance,
    query = plan.pairInput inst ∨ query = plan.conditionInput inst

/-- Difference components obtained by applying one unconditional estimator to
the paired and condition-only queries. -/
def components (plan : Plan)
    (estimate : GapMINKT.Logarithmic.Estimator) : DifferenceEstimator where
  minuend := fun inst => estimate (plan.pairInput inst)
  subtrahend := fun inst => estimate (plan.conditionInput inst)
  correction := plan.correction

/-- The SoI accounting schedule induced by the two ordinary estimator queries.
The lower-estimate losses are exactly the logarithmic slacks supplied by the
unconditional Fact 3.4 sandwich. -/
def accountingSchedule (plan : Plan)
    (ordinaryParameters : GapMINKT.Logarithmic.Parameters) :
    SoIAccountingSchedule where
  soiTime := plan.soiTime
  pairUpperTime := plan.pairInputTime
  pairUpperLoss := plan.pairUpperLoss
  conditionLowerLoss := fun inst =>
    ordinaryParameters.logarithmicSlack (plan.conditionInput inst)
  pairLowerLoss := fun inst =>
    ordinaryParameters.logarithmicSlack (plan.pairInput inst)

end Plan

/-- Operational evidence that the plan's `pairUpperLoss` really gives the
unconditional upper-chain bound used by the SoI argument.

No finiteness is demanded. When the condition minimum `C^t(y)` or the
conditional minimum `C^t(x | y)` is infinite, the upper chain holds trivially,
so the budgets only need to contain the minima that are attained. (Demanding
finite minima at every instance would be unsatisfiable: no machine produces a
nonempty string within zero steps.) -/
structure SupportsPairUpper
    {ordinaryTapes conditionalTapes : ℕ}
    (plan : Plan) (composition : PairCompositionPlan)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes) : Prop where
  /-- The compiler produces `pair x y` from a program for `y` followed by a
  conditional program for `x`. -/
  composes : ∀ inst : MINCKT.Instance,
    TimeBoundedConditionalPairCompositionAt ordinaryMachine ordinaryMachine
      conditionalMachine composition.compile inst.output inst.condition
        inst.time inst.time (plan.pairInputTime inst)
        (composition.conditionBound inst) (composition.resultBound inst)
  /-- Compiler length is additive up to the plan's explicit upper loss. -/
  length_le : ∀ (inst : MINCKT.Instance) conditionProgram resultProgram,
    conditionProgram.length ≤ composition.conditionBound inst →
    resultProgram.length ≤ composition.resultBound inst →
    (composition.compile conditionProgram resultProgram).length ≤
      resultProgram.length + conditionProgram.length + plan.pairUpperLoss inst
  /-- The chosen condition budget contains the condition minimum whenever
  that minimum is attained. -/
  condition_le_bound : ∀ inst : MINCKT.Instance,
    ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition inst.time ≠ ⊤ →
    ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition inst.time ≤
      (composition.conditionBound inst : WithTop ℕ)
  /-- The chosen conditional-result budget contains the conditional minimum
  whenever that minimum is attained. -/
  result_le_bound : ∀ inst : MINCKT.Instance,
    inst.complexity conditionalMachine ≠ ⊤ →
    inst.complexity conditionalMachine ≤
      (composition.resultBound inst : WithTop ℕ)

/-- Clock, upper-chain, and loss compatibility for reusing one unconditional
Fact 3.4 estimator in the SoI difference construction. -/
structure Compatible {ordinaryTapes conditionalTapes : ℕ}
    (plan : Plan) (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (ordinaryParameters : GapMINKT.Logarithmic.Parameters)
    (conditionalParameters : GapMINCKT.Parameters)
    (soiClock soiLoss : ℕ → ℕ) : Prop where
  /-- The gap clock is at least the SoI clock. -/
  soiClock_le_conditionalTime : ∀ inst,
    soiClock (plan.soiTime inst) ≤
      conditionalParameters.transformedTime inst
  /-- The chosen SoI base time contains the whole pair. -/
  soiSize : ∀ inst,
    inst.output.length + inst.condition.length ≤ plan.soiTime inst
  /-- The condition query's source clock is the condition clock in SoI. -/
  conditionInputTime_eq : ∀ inst,
    plan.conditionInputTime inst = soiClock (plan.soiTime inst)
  /-- The final conditional gap clock dominates the transformed condition-query
  clock. In Proposition 6.2 these are `p^4(t + |x| + |y|)` and `p^4(t')`,
  respectively, for `t' = max {t, |x| + |y|}`. -/
  conditionTransformedTime_le : ∀ inst,
    ordinaryParameters.transformedTime (plan.conditionInput inst) ≤
      conditionalParameters.transformedTime inst
  /-- Transforming the paired query clock reaches the ordinary paired clock on
  the right of SoI. -/
  pairTransformedTime_eq : ∀ inst,
    ordinaryParameters.transformedTime (plan.pairInput inst) = plan.soiTime inst
  /-- Unconditional upper chain at the paired query's source clock. -/
  pair_upper : ∀ inst,
    ordinaryMachine.timeBoundedKolmogorovComplexity
          (pair inst.output inst.condition) (plan.pairInputTime inst) ≤
      inst.complexity conditionalMachine +
          ordinaryMachine.timeBoundedKolmogorovComplexity
            inst.condition inst.time +
        (plan.pairUpperLoss inst : WithTop ℕ)
  /-- The correction pays the condition estimator's logarithmic loss and the
  paired upper-chain loss. -/
  upperLoss_budget : ∀ inst,
    ordinaryParameters.logarithmicSlack (plan.conditionInput inst) +
        plan.pairUpperLoss inst ≤
      plan.correction inst
  /-- The conditional logarithmic slack pays the paired estimator loss, SoI
  loss, and centering correction. -/
  lowerLoss_budget : ∀ inst,
    ordinaryParameters.logarithmicSlack (plan.pairInput inst) +
          soiLoss (plan.soiTime inst) + plan.correction inst ≤
      conditionalParameters.logarithmicSlack inst

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
