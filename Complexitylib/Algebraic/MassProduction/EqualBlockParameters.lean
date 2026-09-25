/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CodeParameters
public import Complexitylib.Algebraic.MassProduction.Growth

/-!
# Two-block base-case parameters

This module fixes the recovery-code dimension for the equal-block base case,
proves the scheduler-capacity inequality below rate one half, and bounds the
one-copy resource bank at the full two-block Shannon scale.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters
open GroupedScheduler

/-- A concrete recovery-code dimension for the two-block base case.  The
factor three leaves a strict direction-capacity margin at every rational rate
strictly below one half. -/
def twoBlockDimension (denominator : Nat) : Nat :=
  3 * denominator

theorem twoBlockDimension_positive
    (denominatorPositive : 0 < denominator) :
    0 < twoBlockDimension denominator := by
  unfold twoBlockDimension
  omega

theorem twoBlockDimension_atLeastTwo
    (denominatorPositive : 0 < denominator) :
    2 <= twoBlockDimension denominator := by
  unfold twoBlockDimension
  omega

/-- Exact exponent inequality behind the two-block scheduler.  It uses only
the information-rate lower bound forced by successful prefix packing. -/
theorem twoBlock_loadExponent
    (numerator denominator prefixWidth width : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (widthPositive : 0 < width)
    (packingRate : prefixWidth <=
      (twoBlockDimension denominator + 1) * width) :
    numerator * (prefixWidth + prefixWidth) / denominator + width <
      width * (twoBlockDimension denominator - 1) := by
  let dimension := twoBlockDimension denominator
  let exponent := numerator * (prefixWidth + prefixWidth) / denominator
  have rateBound : 2 * numerator <= denominator - 1 := by omega
  have divided : exponent * denominator <=
      2 * numerator * prefixWidth := by
    calc
      exponent * denominator <=
          numerator * (prefixWidth + prefixWidth) := by
        exact Nat.div_mul_le_self _ _
      _ = 2 * numerator * prefixWidth := by ring
  have coefficientGap :
      (denominator - 1) * (dimension + 1) <
        denominator * (dimension - 2) := by
    have denominatorEq : denominator = (denominator - 1) + 1 := by omega
    have dimensionMinus : dimension - 2 =
        3 * (denominator - 1) + 1 := by
      dsimp [dimension]
      unfold twoBlockDimension
      omega
    have dimensionPlus : dimension + 1 =
        3 * (denominator - 1) + 4 := by
      dsimp [dimension]
      unfold twoBlockDimension
      omega
    rw [denominatorEq, dimensionMinus, dimensionPlus]
    simp only [Nat.add_sub_cancel]
    nlinarith
  have scaledExponent :
      exponent * (denominator * (dimension + 1)) <
        (width * (dimension - 2)) *
          (denominator * (dimension + 1)) := by
    calc
      exponent * (denominator * (dimension + 1)) =
          exponent * denominator * (dimension + 1) := by ring
      _ <= (2 * numerator * prefixWidth) * (dimension + 1) := by
        gcongr
      _ <= ((denominator - 1) * prefixWidth) * (dimension + 1) := by
        gcongr
      _ <= ((denominator - 1) * ((dimension + 1) * width)) *
          (dimension + 1) := by
        gcongr
      _ = ((denominator - 1) * (dimension + 1)) *
          ((dimension + 1) * width) := by ring
      _ < (denominator * (dimension - 2)) *
          ((dimension + 1) * width) := by
        exact Nat.mul_lt_mul_of_pos_right coefficientGap (by positivity)
      _ = (width * (dimension - 2)) *
          (denominator * (dimension + 1)) := by ring
  have exponentSmall : exponent < width * (dimension - 2) :=
    Nat.lt_of_mul_lt_mul_right scaledExponent
  change exponent + width < width * (dimension - 1)
  calc
    exponent + width < width * (dimension - 2) + width :=
      Nat.add_lt_add_right exponentSmall width
    _ = width * (dimension - 1) := by
      have dimensionAtLeast : 2 <= dimension := by
        dsimp [dimension]
        exact twoBlockDimension_atLeastTwo denominatorPositive
      have dimensionStep : dimension - 1 = (dimension - 2) + 1 := by omega
      rw [dimensionStep, Nat.mul_add, Nat.mul_one]

/-- For one request group, every allowed two-block batch has enough
projective directions for the least admissible field selected by
`CodeParameters`. -/
theorem twoBlock_loadBound
    (numerator denominator prefixWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (copiesBound : copies <=
      2 ^ (numerator * (prefixWidth + prefixWidth) / denominator)) :
    requestGroupSize copies 1 *
        2 ^ fieldWidth prefixWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive) <
      2 ^ (fieldWidth prefixWidth (twoBlockDimension denominator)
          (twoBlockDimension_positive denominatorPositive) *
        (twoBlockDimension denominator - 1)) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth prefixWidth dimension dimensionPositive
  have widthPositive := fieldWidth_positive prefixWidth dimension
    dimensionPositive
  have packingRate :=
    prefixWidth_le_succ_dimension_mul_fieldWidth prefixWidth dimension
      dimensionPositive
  have exponentSmall := twoBlock_loadExponent numerator denominator
    prefixWidth width denominatorPositive rateBelowHalf widthPositive
    packingRate
  have powerBound :
      2 ^ (numerator * (prefixWidth + prefixWidth) / denominator + width) <
        2 ^ (width * (dimension - 1)) :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 exponentSmall
  calc
    requestGroupSize copies 1 * 2 ^ width = copies * 2 ^ width := by
      simp [requestGroupSize]
    _ <= 2 ^ (numerator * (prefixWidth + prefixWidth) / denominator) *
        2 ^ width := Nat.mul_le_mul_right _ copiesBound
    _ = 2 ^ (numerator * (prefixWidth + prefixWidth) / denominator +
        width) := (Nat.pow_add _ _ _).symm
    _ < 2 ^ (width * (dimension - 1)) := powerBound

/-- The concrete Shannon bound supplied to every one-copy resource circuit in
the two-block base case. -/
def twoBlockResourceBound (blockWidth : Nat) : Nat :=
  27 * 2 ^ blockWidth / blockWidth

/-- The recursive resource bank already lies at the sharp Shannon scale for
the complete two-block input. -/
theorem twoBlock_resourceTerm_le
    (denominator blockWidth : Nat)
    (denominatorPositive : 0 < denominator)
    (blockPositive : 0 < blockWidth) :
    ResourceEvaluation.resourceBitCount
          (twoBlockDimension denominator)
          (fieldWidth blockWidth (twoBlockDimension denominator)
            (twoBlockDimension_positive denominatorPositive)) *
        twoBlockResourceBound blockWidth <=
      (216 * resourceConstant (twoBlockDimension denominator)) *
        (2 ^ (blockWidth + blockWidth) /
          (blockWidth + blockWidth)) := by
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let resourceScale := 2 ^ (blockWidth + blockWidth) /
    (blockWidth + blockWidth)
  have countBound := resourceBitCount_le blockWidth dimension dimensionPositive
  have twiceFits : 2 * blockWidth <= 2 ^ (blockWidth + blockWidth) := by
    calc
      2 * blockWidth <= 2 ^ blockWidth :=
        Nat.mul_le_pow (by decide : 2 ≠ 1) blockWidth
      _ <= 2 ^ (blockWidth + blockWidth) :=
        Nat.pow_le_pow_right (by omega) (by omega)
  have quotientBound := Growth.div_le_four_mul_double_div
    (2 ^ (blockWidth + blockWidth)) blockWidth blockPositive twiceFits
  have quotientBound' :
      2 ^ (blockWidth + blockWidth) / blockWidth <= 4 * resourceScale := by
    simpa only [resourceScale, two_mul] using quotientBound
  have blockFits : blockWidth <= 2 ^ (blockWidth + blockWidth) :=
    (by omega : blockWidth <= 2 * blockWidth).trans twiceFits
  change ResourceEvaluation.resourceBitCount dimension width *
      (27 * 2 ^ blockWidth / blockWidth) <=
    (216 * resourceConstant dimension) * resourceScale
  calc
    ResourceEvaluation.resourceBitCount dimension width *
        (27 * 2 ^ blockWidth / blockWidth) <=
      (resourceConstant dimension * 2 ^ blockWidth) *
        (27 * 2 ^ blockWidth / blockWidth) := by
      gcongr
    _ <= ((resourceConstant dimension * 2 ^ blockWidth) *
        (27 * 2 ^ blockWidth)) / blockWidth :=
      Nat.mul_div_le_mul_div_assoc
        (resourceConstant dimension * 2 ^ blockWidth)
        (27 * 2 ^ blockWidth) blockWidth
    _ = (27 * resourceConstant dimension *
        2 ^ (blockWidth + blockWidth)) / blockWidth := by
      rw [Nat.pow_add]
      apply congrArg (fun value => value / blockWidth)
      ring
    _ <= 2 * (27 * resourceConstant dimension) *
        (2 ^ (blockWidth + blockWidth) / blockWidth) := by
      exact Growth.mul_div_le_two_mul_mul_div
        (27 * resourceConstant dimension)
        (2 ^ (blockWidth + blockWidth)) blockWidth blockPositive blockFits
    _ <= 2 * (27 * resourceConstant dimension) *
        (4 * resourceScale) := by gcongr
    _ = (216 * resourceConstant dimension) * resourceScale := by ring

end EqualBlock
end MassProduction
end Algebraic
