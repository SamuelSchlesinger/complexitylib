/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BlockInductionFiniteStep
public import Complexitylib.Algebraic.MassProduction.Padding

/-!
# Arbitrary-width block induction step

This module pads arbitrary input widths to equal-block multiples, transports
the finite-step Shannon bound back across that padding, and exposes the
rate-raising theorem `massProducesAt_step`.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BlockInduction

open CodeParameters

/-! ## Padding arbitrary widths to equal blocks -/

/-- Compatibility name for the generic Shannon-scale padding bound. -/
theorem shannonScale_le_of_le_add
    (inputWidth targetWidth padding : Nat)
    (inputPositive : 0 < inputWidth)
    (fits : inputWidth <= targetWidth)
    (upper : targetWidth <= inputWidth + padding) :
    2 ^ targetWidth / targetWidth <=
      (2 * 2 ^ padding) * (2 ^ inputWidth / inputWidth) :=
  _root_.Algebraic.MassProduction.shannonScale_le_of_le_add
    inputWidth targetWidth padding inputPositive fits upper

/-- Smallest equal-block width whose complete input covers `inputWidth`. -/
def blockCeil (level inputWidth : Nat) : Nat :=
  inputWidth ⌈/⌉ (level + 1)

/-- Least multiple of `level + 1` represented by the equal-block layout. -/
def nextEqualBlockWidth (level inputWidth : Nat) : Nat :=
  stepInputWidth level (blockCeil level inputWidth)

theorem inputWidth_le_nextEqualBlockWidth
    (level inputWidth : Nat) :
    inputWidth <= nextEqualBlockWidth level inputWidth := by
  have capacity : inputWidth <=
      (level + 1) * (inputWidth ⌈/⌉ (level + 1)) :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < level + 1)).mp le_rfl
  unfold nextEqualBlockWidth stepInputWidth blockCeil
  calc
    inputWidth <= (level + 1) * (inputWidth ⌈/⌉ (level + 1)) := capacity
    _ = inputWidth ⌈/⌉ (level + 1) +
        level * (inputWidth ⌈/⌉ (level + 1)) := by ring

theorem nextEqualBlockWidth_le_add
    (level inputWidth : Nat) :
    nextEqualBlockWidth level inputWidth <= inputWidth + (level + 1) := by
  let divisor := level + 1
  have divisorPositive : 0 < divisor := by omega
  have ceiling := CodeParameters.ceilDiv_le_div_add_one inputWidth divisor
    divisorPositive
  have floor := Nat.mul_div_le inputWidth divisor
  unfold nextEqualBlockWidth stepInputWidth blockCeil
  dsimp [divisor] at ceiling floor
  calc
    inputWidth ⌈/⌉ (level + 1) +
        level * (inputWidth ⌈/⌉ (level + 1)) =
      (level + 1) * (inputWidth ⌈/⌉ (level + 1)) := by ring
    _ <= (level + 1) * (inputWidth / (level + 1) + 1) := by gcongr
    _ = (level + 1) * (inputWidth / (level + 1)) +
        (level + 1) := by ring
    _ <= inputWidth + (level + 1) := Nat.add_le_add_right floor _

theorem shannonScale_nextEqualBlockWidth_le
    (level inputWidth : Nat)
    (inputPositive : 0 < inputWidth) :
    2 ^ nextEqualBlockWidth level inputWidth /
        nextEqualBlockWidth level inputWidth <=
      (2 * 2 ^ (level + 1)) * (2 ^ inputWidth / inputWidth) :=
  shannonScale_le_of_le_add inputWidth
    (nextEqualBlockWidth level inputWidth) (level + 1) inputPositive
    (inputWidth_le_nextEqualBlockWidth level inputWidth)
    (nextEqualBlockWidth_le_add level inputWidth)

/-- The manuscript's equal-block induction step on arbitrary sufficiently
large input widths. -/
theorem massProducesAt_step
    (level numerator denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (previous : MassProducesAt
      (groupRateNumerator level denominator)
      (groupRateDenominator denominator * level)) :
    MassProducesAt numerator denominator := by
  obtain ⟨equalConstant, eventualEqualBound⟩ :=
    eventually_step_mass_bound level numerator denominator levelAtLeastTwo
      denominatorPositive rateBelowLevel previous
  obtain ⟨blockCutoff, equalBound⟩ :=
    Filter.eventually_atTop.1 eventualEqualBound
  refine ⟨(2 * 2 ^ (level + 1)) * equalConstant,
    (level + 1) * blockCutoff, ?_⟩
  intro inputWidth inputPositive pastCutoff function copies copiesPositive
    copiesBound
  let blockWidth := blockCeil level inputWidth
  let paddedWidth := nextEqualBlockWidth level inputWidth
  have fits : inputWidth <= paddedWidth :=
    inputWidth_le_nextEqualBlockWidth level inputWidth
  have blockPastCutoff : blockCutoff <= blockWidth := by
    have capacity : inputWidth <= (level + 1) * blockWidth := by
      dsimp [blockWidth, blockCeil]
      exact (ceilDiv_le_iff_le_mul (by omega : 0 < level + 1)).mp le_rfl
    have scaled : (level + 1) * blockCutoff <=
        (level + 1) * blockWidth := pastCutoff.trans capacity
    exact Nat.le_of_mul_le_mul_left scaled (by omega)
  have paddedCopiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator) := by
    have widened := copiesBound.trans
      (rationalCopyBudget_mono_inputs
        (numerator := numerator) (denominator := denominator) fits)
    simpa [rationalCopyBudget, paddedWidth, nextEqualBlockWidth] using widened
  let paddedFunction := InputSplit.paddedFunction fits function
  have paddedMass := equalBound blockWidth blockPastCutoff paddedFunction
    copies copiesPositive paddedCopiesBound
  have transport := InputSplit.booleanMassComplexity_le_paddedFunction
    inputPositive fits function copies
  have scaleBound := shannonScale_nextEqualBlockWidth_le level inputWidth
    inputPositive
  calc
    booleanMassComplexity function copies <=
        booleanMassComplexity paddedFunction copies := transport
    _ <= (equalConstant *
          (2 ^ stepInputWidth level blockWidth /
            stepInputWidth level blockWidth) : Nat) := paddedMass
    _ = (equalConstant * (2 ^ paddedWidth / paddedWidth) : Nat) := by rfl
    _ <= (((2 * 2 ^ (level + 1)) * equalConstant) *
          (2 ^ inputWidth / inputWidth) : Nat) := by
      exact_mod_cast (calc
        equalConstant * (2 ^ paddedWidth / paddedWidth) <=
            equalConstant * ((2 * 2 ^ (level + 1)) *
              (2 ^ inputWidth / inputWidth)) := by gcongr
        _ = ((2 * 2 ^ (level + 1)) * equalConstant) *
            (2 ^ inputWidth / inputWidth) := by ring)

end BlockInduction
end MassProduction
end Algebraic
