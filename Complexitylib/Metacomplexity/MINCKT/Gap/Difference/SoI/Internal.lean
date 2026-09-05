/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Difference.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Depth.Internal

/-!
# SoI accounting for conditional-complexity difference estimators -- internals
-/


public section

namespace Complexity

private theorem withTopNat_add_le_add_internal
    {first second third fourth : WithTop ℕ}
    (hfirst : first ≤ third) (hsecond : second ≤ fourth) :
    first + second ≤ third + fourth := by
  induction first using WithTop.recTopCoe with
  | top =>
      have hthird : third = ⊤ := top_unique hfirst
      subst third
      simp
  | coe firstValue =>
      induction second using WithTop.recTopCoe with
      | top =>
          have hfourth : fourth = ⊤ := top_unique hsecond
          subst fourth
          simp
      | coe secondValue =>
          induction third using WithTop.recTopCoe with
          | top => simp
          | coe thirdValue =>
              induction fourth using WithTop.recTopCoe with
              | top => simp
              | coe fourthValue =>
                  exact WithTop.coe_le_coe.mpr <|
                    Nat.add_le_add (WithTop.coe_le_coe.mp hfirst)
                      (WithTop.coe_le_coe.mp hsecond)

namespace GapMINCKT

namespace DifferenceEstimator

theorem SatisfiesSoIInputs.satisfiesAccounting_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {components : DifferenceEstimator} {schedule : SoIAccountingSchedule}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : Parameters} {soiClock soiLoss : ℕ → ℕ}
    (hinputs : components.SatisfiesSoIInputs schedule ordinaryMachine
      conditionalMachine parameters soiClock soiLoss)
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine soiClock soiLoss)
    (hwidening : parameters.IsWidening) :
    components.SatisfiesAccounting ordinaryMachine conditionalMachine
      parameters := by
  constructor
  · intro inst
    have hdepth := TM.computationalDepthBetween_add_later_internal
      ordinaryMachine inst.condition
        (hwidening inst.output.length inst.condition.length inst.time)
    have hlater := hinputs.condition_lower inst
    have hdepthLater :
        ordinaryMachine.computationalDepthBetween inst.condition inst.time
              (parameters.transformedTime inst) +
            ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
              (parameters.transformedTime inst) ≤
          ordinaryMachine.computationalDepthBetween inst.condition inst.time
              (parameters.transformedTime inst) +
            (components.subtrahend inst +
              schedule.conditionLowerLoss inst : ℕ) :=
      withTopNat_add_le_add_internal le_rfl hlater
    have hconditionalDepth :
        inst.complexity conditionalMachine +
              (ordinaryMachine.computationalDepthBetween inst.condition
                    inst.time (parameters.transformedTime inst) +
                ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
                  (parameters.transformedTime inst)) ≤
          inst.complexity conditionalMachine +
            (ordinaryMachine.computationalDepthBetween inst.condition inst.time
                  (parameters.transformedTime inst) +
              (components.subtrahend inst +
                schedule.conditionLowerLoss inst : ℕ)) :=
      withTopNat_add_le_add_internal le_rfl hdepthLater
    have hupperLoss :
        (inst.complexity conditionalMachine +
              (ordinaryMachine.computationalDepthBetween inst.condition
                    inst.time (parameters.transformedTime inst) +
                ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
                  (parameters.transformedTime inst))) +
            schedule.pairUpperLoss inst ≤
          (inst.complexity conditionalMachine +
            (ordinaryMachine.computationalDepthBetween inst.condition inst.time
                  (parameters.transformedTime inst) +
              (components.subtrahend inst +
                schedule.conditionLowerLoss inst : ℕ))) +
            schedule.pairUpperLoss inst :=
      withTopNat_add_le_add_internal hconditionalDepth le_rfl
    have hpair := hinputs.pair_upper inst
    rw [← hdepth] at hpair
    have hbeforeBudget :=
      (hinputs.minuend_upper inst).trans (hpair.trans hupperLoss)
    have htailValue :
        components.subtrahend inst + schedule.conditionLowerLoss inst +
            schedule.pairUpperLoss inst ≤
          components.subtrahend inst + components.correction inst := by
      simpa only [Nat.add_assoc] using
        Nat.add_le_add_left (hinputs.upperLoss_budget inst)
          (components.subtrahend inst)
    have htail :
        ((components.subtrahend inst + schedule.conditionLowerLoss inst : ℕ) :
            WithTop ℕ) + schedule.pairUpperLoss inst ≤
          (components.subtrahend inst + components.correction inst : ℕ) := by
      exact WithTop.coe_le_coe.mpr htailValue
    have hbudget :
        (inst.complexity conditionalMachine +
              ordinaryMachine.computationalDepthBetween inst.condition inst.time
                (parameters.transformedTime inst)) +
            (((components.subtrahend inst +
                schedule.conditionLowerLoss inst : ℕ) : WithTop ℕ) +
              schedule.pairUpperLoss inst) ≤
          (inst.complexity conditionalMachine +
              ordinaryMachine.computationalDepthBetween inst.condition inst.time
                (parameters.transformedTime inst)) +
            (components.subtrahend inst + components.correction inst : ℕ) :=
      withTopNat_add_le_add_internal le_rfl htail
    exact hbeforeBudget.trans (by
      simpa only [add_assoc] using hbudget)
  · intro inst
    have hchain := hsoi.chain_le inst.output inst.condition
      (schedule.soiTime inst) (hinputs.soiSize inst)
    have hconditionalClock :=
      OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
        conditionalMachine inst.output inst.condition
          (hinputs.soiClock_le_transformedTime inst)
    have hcondition :
        (inst.withTime (parameters.transformedTime inst)).complexity
              conditionalMachine + components.subtrahend inst ≤
          conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
                inst.output inst.condition (soiClock (schedule.soiTime inst)) +
            ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
              (soiClock (schedule.soiTime inst)) :=
      withTopNat_add_le_add_internal hconditionalClock
        (hinputs.condition_upper inst)
    have hconditionCorrection :
        ((inst.withTime (parameters.transformedTime inst)).complexity
              conditionalMachine + components.subtrahend inst) +
            components.correction inst ≤
          (conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
                inst.output inst.condition (soiClock (schedule.soiTime inst)) +
              ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
                (soiClock (schedule.soiTime inst))) +
            components.correction inst :=
      withTopNat_add_le_add_internal hcondition le_rfl
    have hchainCorrection :
        (conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
                inst.output inst.condition (soiClock (schedule.soiTime inst)) +
              ordinaryMachine.timeBoundedKolmogorovComplexity inst.condition
                (soiClock (schedule.soiTime inst))) +
            components.correction inst ≤
          (ordinaryMachine.timeBoundedKolmogorovComplexity
                (pair inst.output inst.condition) (schedule.soiTime inst) +
              soiLoss (schedule.soiTime inst)) +
            components.correction inst :=
      withTopNat_add_le_add_internal hchain le_rfl
    have hpairLoss :
        ordinaryMachine.timeBoundedKolmogorovComplexity
              (pair inst.output inst.condition) (schedule.soiTime inst) +
            soiLoss (schedule.soiTime inst) ≤
          (components.minuend inst + schedule.pairLowerLoss inst : ℕ) +
            soiLoss (schedule.soiTime inst) :=
      withTopNat_add_le_add_internal (hinputs.pair_lower inst) le_rfl
    have hpairLossCorrection :
        (ordinaryMachine.timeBoundedKolmogorovComplexity
              (pair inst.output inst.condition) (schedule.soiTime inst) +
            soiLoss (schedule.soiTime inst)) + components.correction inst ≤
          ((components.minuend inst + schedule.pairLowerLoss inst : ℕ) +
              soiLoss (schedule.soiTime inst)) +
            components.correction inst :=
      withTopNat_add_le_add_internal hpairLoss le_rfl
    have hbudgetValue :
        components.minuend inst + schedule.pairLowerLoss inst +
              soiLoss (schedule.soiTime inst) + components.correction inst ≤
          components.minuend inst + parameters.logarithmicSlack inst := by
      simpa only [Nat.add_assoc] using
        Nat.add_le_add_left (hinputs.lowerLoss_budget inst)
          (components.minuend inst)
    have hbudget :
        (((components.minuend inst + schedule.pairLowerLoss inst : ℕ) :
              WithTop ℕ) + soiLoss (schedule.soiTime inst)) +
            components.correction inst ≤
          (components.minuend inst + parameters.logarithmicSlack inst : ℕ) := by
      exact WithTop.coe_le_coe.mpr hbudgetValue
    have hresult := hconditionCorrection.trans <|
      hchainCorrection.trans <| hpairLossCorrection.trans hbudget
    simpa only [add_assoc, Nat.cast_add] using hresult

end DifferenceEstimator

end GapMINCKT

end Complexity
