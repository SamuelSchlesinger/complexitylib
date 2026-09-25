/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Internal

/-!
# The iterated-clock schedule in the conditional MinKT reduction

This module constructs the exact `p`, `p^2`, `p^3`, and `p^4` query schedule
from Proposition 6.2. A regular primitive clock, explicit finite loss budget,
and the already-formalized paired upper-chain theorem produce the complete
`Compatible` contract for reducing conditional gap MinKT to two ordinary gap
MinKT estimator queries.
-/


public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

@[simp] theorem clockIterate_zero (clock : ℕ → ℕ) (time : ℕ) :
    clockIterate clock 0 time = time :=
  clockIterate_zero_internal clock time

@[simp] theorem clockIterate_succ (clock : ℕ → ℕ)
    (iterations time : ℕ) :
    clockIterate clock (iterations + 1) time =
      clock (clockIterate clock iterations time) :=
  clockIterate_succ_internal clock iterations time

/-- Every fixed iterate of a monotone primitive clock is monotone. -/
theorem clockIterate_monotone {clock : ℕ → ℕ}
    (hclock : Monotone clock) (iterations : ℕ) :
    Monotone (clockIterate clock iterations) :=
  clockIterate_monotone_internal hclock iterations

/-- Repeated application of a widening primitive clock only increases time. -/
theorem clockIterate_dominates {clock : ℕ → ℕ}
    (hclock : ∀ time, time ≤ clock time) (iterations time : ℕ) :
    time ≤ clockIterate clock iterations time :=
  clockIterate_dominates_internal hclock iterations time

theorem paddedTime_size_le (inst : MINCKT.Instance) :
    inst.output.length + inst.condition.length ≤ paddedTime inst :=
  paddedTime_size_le_internal inst

theorem paddedTime_time_le (inst : MINCKT.Instance) :
    inst.time ≤ paddedTime inst :=
  paddedTime_time_le_internal inst

theorem paddedTime_le_total (inst : MINCKT.Instance) :
    paddedTime inst ≤ inst.time + inst.output.length + inst.condition.length :=
  paddedTime_le_total_internal inst

@[simp] theorem ordinaryParameters_transformedTime (clock : ℕ → ℕ)
    (inst : MINKT.Instance) :
    (ordinaryParameters clock).transformedTime inst = clock inst.time :=
  ordinaryParameters_transformedTime_internal clock inst

@[simp] theorem conditionalParameters_transformedTime (clock : ℕ → ℕ)
    (inst : MINCKT.Instance) :
    (conditionalParameters clock).transformedTime inst =
      clockIterate clock 4
        (inst.time + inst.output.length + inst.condition.length) :=
  conditionalParameters_transformedTime_internal clock inst

@[simp] theorem plan_pairInputTime (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).pairInputTime inst =
      clockIterate clock 1 (paddedTime inst) :=
  plan_pairInputTime_internal clock pairUpperLoss correction inst

@[simp] theorem plan_conditionInputTime (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).conditionInputTime inst =
      clockIterate clock 3 (paddedTime inst) :=
  plan_conditionInputTime_internal clock pairUpperLoss correction inst

@[simp] theorem plan_soiTime (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).soiTime inst =
      clockIterate clock 2 (paddedTime inst) :=
  plan_soiTime_internal clock pairUpperLoss correction inst

@[simp] theorem plan_pairUpperLoss (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).pairUpperLoss inst =
      pairUpperLoss inst :=
  plan_pairUpperLoss_internal clock pairUpperLoss correction inst

@[simp] theorem plan_correction (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).correction inst = correction inst :=
  plan_correction_internal clock pairUpperLoss correction inst

/-- A regular clock makes the one-step ordinary gap transform widening. -/
theorem IsRegularClock.ordinaryParameters_widening
    {clock : ℕ → ℕ} (hclock : IsRegularClock clock) :
    (ordinaryParameters clock).IsWidening :=
  hclock.ordinaryParameters_widening_internal

/-- A regular clock makes the final four-step conditional transform widening. -/
theorem IsRegularClock.conditionalParameters_widening
    {clock : ℕ → ℕ} (hclock : IsRegularClock clock) :
    (conditionalParameters clock).IsWidening :=
  hclock.conditionalParameters_widening_internal

/-- The full-domain estimator sandwich is unsatisfiable for the iterated
plan's ordinary parameters: their transformed clock ignores output length, so at
source time `0` no machine prints a string longer than `clock 0`. The
consequences therefore require the sandwich only on the plan's own estimator
queries (`SatisfiesBoundsOn`). -/
theorem not_satisfiesBounds_ordinaryParameters {tapes : ℕ} (machine : TM tapes)
    (clock : ℕ → ℕ) (estimate : GapMINKT.Logarithmic.Estimator) :
    ¬ estimate.SatisfiesBounds machine (ordinaryParameters clock) :=
  not_satisfiesBounds_ordinaryParameters_internal machine clock estimate

/-- The exact iterated clocks and finite loss inequalities discharge every
non-machine field of the unconditional-estimator compatibility contract. -/
theorem IsRegularClock.compatible
    {ordinaryTapes conditionalTapes : ℕ}
    {clock soiLoss : ℕ → ℕ}
    {pairUpperLoss correction : MINCKT.Instance → ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hloss : LossBudget clock pairUpperLoss correction soiLoss)
    (hpair : ∀ inst,
      ordinaryMachine.timeBoundedKolmogorovComplexity
            (pair inst.output inst.condition)
              ((plan clock pairUpperLoss correction).pairInputTime inst) ≤
        inst.complexity conditionalMachine +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              inst.condition inst.time +
          ((plan clock pairUpperLoss correction).pairUpperLoss inst : WithTop ℕ)) :
    Compatible (plan clock pairUpperLoss correction) ordinaryMachine
      conditionalMachine (ordinaryParameters clock) (conditionalParameters clock)
        clock soiLoss :=
  hclock.compatible_internal hloss hpair

/-- Combining the operational condition-first compiler with the exact
iterated-clock/loss schedule yields the complete compatibility contract. -/
theorem IsRegularClock.compatible_of_pairComposition
    {ordinaryTapes conditionalTapes : ℕ}
    {clock soiLoss : ℕ → ℕ}
    {pairUpperLoss correction : MINCKT.Instance → ℕ}
    {composition : PairCompositionPlan}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hloss : LossBudget clock pairUpperLoss correction soiLoss)
    (hsupports : SupportsPairUpper (plan clock pairUpperLoss correction)
      composition ordinaryMachine conditionalMachine) :
    Compatible (plan clock pairUpperLoss correction) ordinaryMachine
      conditionalMachine (ordinaryParameters clock) (conditionalParameters clock)
        clock soiLoss :=
  hclock.compatible_of_pairComposition_internal hloss hsupports

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
