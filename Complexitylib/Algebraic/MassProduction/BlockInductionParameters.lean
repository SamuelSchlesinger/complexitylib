/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.EqualBlock

/-!
# Equal-block induction parameters

This module defines the request-group exponents used by one fixed-exponent
induction step and proves the scheduler-capacity inequalities they satisfy.
All rates and floor operations remain explicit natural-number arithmetic.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BlockInduction

open CodeParameters
open GroupedScheduler

/-- The recovery-code dimension used at every non-base induction step. -/
def stepDimension (denominator : Nat) : Nat :=
  12 * denominator

theorem stepDimension_positive
    (denominatorPositive : 0 < denominator) :
    0 < stepDimension denominator := by
  unfold stepDimension
  omega

theorem stepDimension_atLeastTwo
    (denominatorPositive : 0 < denominator) :
    2 <= stepDimension denominator := by
  unfold stepDimension
  omega

/-- Numerator of the group exponent in block units.  It is one integer below
the `(k - 1)`-block threshold at denominator `2 * denominator`. -/
def groupRateNumerator (level denominator : Nat) : Nat :=
  2 * denominator * (level - 1) - 1

/-- Denominator used to express the group exponent in block units. -/
def groupRateDenominator (denominator : Nat) : Nat :=
  2 * denominator

/-- Floored base-two exponent of the number of request groups. -/
def groupExponent (level denominator blockWidth : Nat) : Nat :=
  groupRateNumerator level denominator * blockWidth /
    groupRateDenominator denominator

/-- Exact power-of-two number of request groups at one induction step. -/
def groupCount (level denominator blockWidth : Nat) : Nat :=
  2 ^ groupExponent level denominator blockWidth

theorem groupRateNumerator_add_one
    (level denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator) :
    groupRateNumerator level denominator + 1 =
      2 * denominator * (level - 1) := by
  unfold groupRateNumerator
  have levelMinusPositive : 0 < level - 1 := by omega
  have productPositive : 0 < 2 * denominator * (level - 1) := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) denominatorPositive)
      levelMinusPositive
  exact Nat.sub_add_cancel productPositive

theorem groupRate_below_previousLevel
    (level denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator) :
    level * groupRateNumerator level denominator <
      (level - 1) * (groupRateDenominator denominator * level) := by
  have numeratorStep := groupRateNumerator_add_one level denominator
    levelAtLeastTwo denominatorPositive
  unfold groupRateDenominator
  have levelPositive : 0 < level := by omega
  have identity :
      level * (2 * denominator * (level - 1)) =
        (level - 1) * (2 * denominator * level) := by ring
  calc
    level * groupRateNumerator level denominator <
        level * (groupRateNumerator level denominator + 1) := by
      exact Nat.mul_lt_mul_of_pos_left
        (Nat.lt_succ_self (groupRateNumerator level denominator))
        levelPositive
    _ = level * (2 * denominator * (level - 1)) := by
      rw [numeratorStep]
    _ = (level - 1) * (2 * denominator * level) := identity

theorem groupCount_positive
    (level denominator blockWidth : Nat) :
    0 < groupCount level denominator blockWidth := by
  unfold groupCount
  positivity

/-- The group count is exactly within the recursive rational copy budget on
the `level * blockWidth` suffix. -/
theorem groupCount_le_recursiveBudget
    (level denominator blockWidth : Nat)
    (levelPositive : 0 < level) :
    groupCount level denominator blockWidth <=
      rationalCopyBudget (groupRateNumerator level denominator)
        (groupRateDenominator denominator * level)
        (level * blockWidth) := by
  unfold groupCount groupExponent rationalCopyBudget
  have rescaled := Nat.mul_div_mul_right
    (groupRateNumerator level denominator * blockWidth)
    (groupRateDenominator denominator) levelPositive
  have numeratorIdentity :
      groupRateNumerator level denominator * (level * blockWidth) =
        (groupRateNumerator level denominator * blockWidth) * level := by
    ring
  have denominatorIdentity :
      groupRateDenominator denominator * level =
        groupRateDenominator denominator * level := rfl
  rw [numeratorIdentity, denominatorIdentity, rescaled]

/-- A single rational exponent dominates the request load left in one group.
The extra half-margin absorbs the one-unit loss from adding two floors. -/
def groupLoadExponent (denominator blockWidth : Nat) : Nat :=
  (4 * denominator - 1) * blockWidth / (4 * denominator)

theorem requestExponent_le_group_add_load
    (level numerator denominator blockWidth : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth) :
    numerator * ((level + 1) * blockWidth) / denominator <=
      groupExponent level denominator blockWidth +
        groupLoadExponent denominator blockWidth := by
  let groupNumerator := groupRateNumerator level denominator
  let twiceDenominator := 2 * denominator
  have targetCoefficient :
      2 * ((level + 1) * numerator) <=
        groupNumerator + (2 * denominator - 1) := by
    have groupStep := groupRateNumerator_add_one level denominator
      levelAtLeastTwo denominatorPositive
    dsimp [groupNumerator]
    have targetStep :
        (level + 1) * numerator + 1 <= level * denominator := by
      omega
    have doubled := Nat.mul_le_mul_left 2 targetStep
    have levelDecomposition : level = (level - 1) + 1 := by omega
    have productIdentity :
        2 * (level * denominator) =
          2 * denominator * (level - 1) + 2 * denominator := by
      calc
        2 * (level * denominator) =
            2 * (((level - 1) + 1) * denominator) := by
          exact congrArg (fun value => 2 * (value * denominator))
            levelDecomposition
        _ = 2 * denominator * (level - 1) + 2 * denominator := by ring
    have levelMinusPositive : 0 < level - 1 := by omega
    have leftProductPositive : 0 < 2 * denominator * (level - 1) := by
      exact Nat.mul_pos (Nat.mul_pos (by omega) denominatorPositive)
        levelMinusPositive
    have rightProductPositive : 0 < 2 * denominator := by omega
    calc
      2 * ((level + 1) * numerator) <=
          2 * (level * denominator) - 2 := by omega
      _ = groupRateNumerator level denominator +
          (2 * denominator - 1) := by
        unfold groupRateNumerator
        omega
  have rescaled :
      numerator * ((level + 1) * blockWidth) / denominator =
        (2 * ((level + 1) * numerator) * blockWidth) /
          twiceDenominator := by
    dsimp [twiceDenominator]
    have scaled := Nat.mul_div_mul_left
      (numerator * ((level + 1) * blockWidth)) denominator
      (by omega : 0 < 2)
    rw [show 2 * (numerator * ((level + 1) * blockWidth)) =
      2 * ((level + 1) * numerator) * blockWidth by ring] at scaled
    exact scaled.symm
  have splitBound :
      (2 * ((level + 1) * numerator) * blockWidth) /
          twiceDenominator <=
        (groupNumerator * blockWidth) / twiceDenominator +
          ((2 * denominator - 1) * blockWidth) / twiceDenominator + 1 := by
    have coefficientScaled :
        2 * ((level + 1) * numerator) * blockWidth <=
          (groupNumerator + (2 * denominator - 1)) * blockWidth :=
      Nat.mul_le_mul_right blockWidth targetCoefficient
    calc
      (2 * ((level + 1) * numerator) * blockWidth) /
          twiceDenominator <=
        ((groupNumerator + (2 * denominator - 1)) * blockWidth) /
          twiceDenominator := Nat.div_le_div_right coefficientScaled
      _ = (groupNumerator * blockWidth +
          (2 * denominator - 1) * blockWidth) / twiceDenominator := by
        congr 1
        ring
      _ <= (groupNumerator * blockWidth) / twiceDenominator +
          ((2 * denominator - 1) * blockWidth) / twiceDenominator + 1 :=
        Nat.add_div_le_div_add_div_add_one _ _ _
  have remainderBound :
      ((2 * denominator - 1) * blockWidth) / twiceDenominator + 1 <=
        groupLoadExponent denominator blockWidth := by
    have twicePositive : 0 < twiceDenominator := by
      dsimp [twiceDenominator]
      omega
    have quotientScaled :
        (((2 * denominator - 1) * blockWidth) / twiceDenominator) *
            twiceDenominator <=
          (2 * denominator - 1) * blockWidth :=
      Nat.div_mul_le_self _ _
    unfold groupLoadExponent
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4 * denominator)).2
    calc
      ((((2 * denominator - 1) * blockWidth) / twiceDenominator + 1) *
          (4 * denominator)) =
          2 * ((((2 * denominator - 1) * blockWidth) /
            twiceDenominator) * twiceDenominator) +
            4 * denominator := by
        dsimp [twiceDenominator]
        ring
      _ <= 2 * ((2 * denominator - 1) * blockWidth) +
          4 * denominator := by gcongr
      _ <= (4 * denominator - 1) * blockWidth := by
        have coefficientIdentity :
            2 * (2 * denominator - 1) + 1 = 4 * denominator - 1 := by
          omega
        calc
          2 * ((2 * denominator - 1) * blockWidth) +
              4 * denominator <=
            2 * ((2 * denominator - 1) * blockWidth) +
              blockWidth := Nat.add_le_add_left blockLarge _
          _ = (2 * (2 * denominator - 1) + 1) * blockWidth := by
            ring
          _ = (4 * denominator - 1) * blockWidth := by
            rw [coefficientIdentity]
  rw [rescaled]
  exact splitBound.trans <| by
    unfold groupExponent groupRateDenominator
    dsimp [groupNumerator, twiceDenominator]
    exact Nat.add_le_add_left remainderBound _

/-- Every permitted batch leaves at most `2^groupLoadExponent` requests in a
single request group. -/
theorem requestGroupSize_le
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * ((level + 1) * blockWidth) / denominator)) :
    requestGroupSize copies (groupCount level denominator blockWidth) <=
      2 ^ groupLoadExponent denominator blockWidth := by
  have exponentBound := requestExponent_le_group_add_load level numerator
    denominator blockWidth levelAtLeastTwo denominatorPositive
    rateBelowLevel blockLarge
  apply (ceilDiv_le_iff_le_mul
    (groupCount_positive level denominator blockWidth)).2
  calc
    copies <=
        2 ^ (numerator * ((level + 1) * blockWidth) / denominator) :=
      copiesBound
    _ <= 2 ^ (groupExponent level denominator blockWidth +
        groupLoadExponent denominator blockWidth) :=
      Nat.pow_le_pow_right (by omega) exponentBound
    _ = groupCount level denominator blockWidth *
        2 ^ groupLoadExponent denominator blockWidth := by
      unfold groupCount
      rw [Nat.pow_add]

/-- The exact scheduler-capacity inequality for one induction step. -/
theorem step_loadBound
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesBound : copies <=
      2 ^ (numerator * ((level + 1) * blockWidth) / denominator)) :
    requestGroupSize copies (groupCount level denominator blockWidth) *
        2 ^ fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive) <
      2 ^ (fieldWidth blockWidth (stepDimension denominator)
          (stepDimension_positive denominatorPositive) *
        (stepDimension denominator - 1)) := by
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let loadExponent := groupLoadExponent denominator blockWidth
  have groupBound := requestGroupSize_le level numerator denominator
    blockWidth copies levelAtLeastTwo denominatorPositive rateBelowLevel
    blockLarge copiesBound
  have packingRate := prefixWidth_le_succ_dimension_mul_fieldWidth
    blockWidth dimension dimensionPositive
  have loadScaled :
      loadExponent * (4 * denominator) <=
        (4 * denominator - 1) * blockWidth := by
    dsimp [loadExponent]
    exact Nat.div_mul_le_self _ _
  have coefficientGap :
      (4 * denominator - 1) * (dimension + 1) <
        4 * denominator * (dimension - 2) := by
    dsimp [dimension]
    unfold stepDimension
    have firstStep : 4 * denominator - 1 + 1 = 4 * denominator := by
      omega
    have secondStep : 12 * denominator - 2 + 2 =
        12 * denominator := by omega
    nlinarith
  have scaledLoad :
      loadExponent * (4 * denominator * (dimension + 1)) <
        (width * (dimension - 2)) *
          (4 * denominator * (dimension + 1)) := by
    calc
      loadExponent * (4 * denominator * (dimension + 1)) =
          (loadExponent * (4 * denominator)) * (dimension + 1) := by ring
      _ <= ((4 * denominator - 1) * blockWidth) *
          (dimension + 1) := by gcongr
      _ = ((4 * denominator - 1) * (dimension + 1)) *
          blockWidth := by ring
      _ < (4 * denominator * (dimension - 2)) * blockWidth := by
        exact Nat.mul_lt_mul_of_pos_right coefficientGap (by omega)
      _ <= (4 * denominator * (dimension - 2)) *
          ((dimension + 1) * width) := by gcongr
      _ = (width * (dimension - 2)) *
          (4 * denominator * (dimension + 1)) := by ring
  have loadSmall : loadExponent < width * (dimension - 2) :=
    Nat.lt_of_mul_lt_mul_right scaledLoad
  have exponentSmall : loadExponent + width < width * (dimension - 1) := by
    calc
      loadExponent + width < width * (dimension - 2) + width :=
        Nat.add_lt_add_right loadSmall width
      _ = width * (dimension - 1) := by
        have dimensionAtLeast : 2 <= dimension := by
          dsimp [dimension]
          exact stepDimension_atLeastTwo denominatorPositive
        have step : dimension - 1 = (dimension - 2) + 1 := by omega
        rw [step, Nat.mul_add, Nat.mul_one]
  calc
    requestGroupSize copies (groupCount level denominator blockWidth) *
        2 ^ width <= 2 ^ loadExponent * 2 ^ width := by gcongr
    _ = 2 ^ (loadExponent + width) := (Nat.pow_add _ _ _).symm
    _ < 2 ^ (width * (dimension - 1)) :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 exponentSmall

end BlockInduction
end MassProduction
end Algebraic
