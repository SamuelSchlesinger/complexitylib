/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BlockInductionLedger

/-!
# Exponential live-volume bound for block induction

This module proves that all live-record terms in one equal-block induction
step fit below a single exponential with a fixed strict margin from the full
input width. Its public endpoint is `step_overheadVolume_exponential_le`.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BlockInduction

open CodeParameters
open GroupedScheduler

/-! ## Strict exponent margin for the complete overhead -/

/-- Denominator of the strict common overhead exponent. -/
def stepMarginDenominator (level denominator : Nat) : Nat :=
  24 * denominator * (level + 1)

/-- Floored exponent appearing in the extension-field cardinality bound. -/
def stepFieldExponent (denominator blockWidth : Nat) : Nat :=
  blockWidth / stepDimension denominator

/-- One strict subunit exponent dominating all non-resource volumes. -/
def stepCommonExponent
    (level denominator blockWidth : Nat) : Nat :=
  (stepMarginDenominator level denominator - 1) *
      stepInputWidth level blockWidth /
    stepMarginDenominator level denominator

theorem stepMarginDenominator_positive
    (level denominator : Nat)
    (denominatorPositive : 0 < denominator) :
    0 < stepMarginDenominator level denominator := by
  unfold stepMarginDenominator
  positivity

/-- A scaled block-unit margin implies the common strict subunit exponent on
the complete `(level + 1)`-block input. -/
theorem exponent_le_stepCommonExponent
    (level denominator blockWidth exponent : Nat)
    (denominatorPositive : 0 < denominator)
    (scaledMargin :
      exponent * (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth) :
    exponent <= stepCommonExponent level denominator blockWidth := by
  let marginDenominator := stepMarginDenominator level denominator
  let inputWidth := stepInputWidth level blockWidth
  have marginPositive : 0 < marginDenominator :=
    stepMarginDenominator_positive level denominator denominatorPositive
  have multiplied := Nat.mul_le_mul_right (level + 1) scaledMargin
  have plusInput :
      exponent * marginDenominator + inputWidth <=
        marginDenominator * inputWidth := by
    dsimp [marginDenominator, inputWidth, stepMarginDenominator,
      stepInputWidth]
    convert multiplied using 1 <;> ring
  have marginDecomposition : marginDenominator - 1 + 1 =
      marginDenominator := Nat.sub_add_cancel marginPositive
  apply (Nat.le_div_iff_mul_le marginPositive).2
  change exponent * marginDenominator <=
    (marginDenominator - 1) * inputWidth
  have rhsDecomposition :
      (marginDenominator - 1) * inputWidth + inputWidth =
        marginDenominator * inputWidth := by
    calc
      (marginDenominator - 1) * inputWidth + inputWidth =
          ((marginDenominator - 1) + 1) * inputWidth := by ring
      _ = marginDenominator * inputWidth := by rw [marginDecomposition]
  rw [← rhsDecomposition] at plusInput
  exact Nat.le_of_add_le_add_right plusInput

/-- All four live-volume exponents fit under one fixed exponent strictly
below the total input width. -/
theorem step_volume_exponents_le
    (level numerator denominator blockWidth : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator) :
    let groupExponent := groupExponent level denominator blockWidth
    let loadExponent := groupLoadExponent denominator blockWidth
    let fieldExponent := stepFieldExponent denominator blockWidth
    let requestExponent :=
      numerator * stepInputWidth level blockWidth / denominator
    let commonExponent :=
      stepCommonExponent level denominator blockWidth
    groupExponent + loadExponent + loadExponent + fieldExponent <=
        commonExponent ∧
      groupExponent + loadExponent + fieldExponent <= commonExponent ∧
      requestExponent + fieldExponent <= commonExponent ∧
      groupExponent + blockWidth <= commonExponent := by
  dsimp only
  let groupExp := groupExponent level denominator blockWidth
  let loadExp := groupLoadExponent denominator blockWidth
  let fieldExp := stepFieldExponent denominator blockWidth
  let requestExp :=
    numerator * stepInputWidth level blockWidth / denominator
  let groupNumerator := groupRateNumerator level denominator
  have groupBase : groupExp * (2 * denominator) <=
      groupNumerator * blockWidth := by
    dsimp [groupExp]
    unfold groupExponent groupRateDenominator
    exact Nat.div_mul_le_self _ _
  have loadBase : loadExp * (4 * denominator) <=
      (4 * denominator - 1) * blockWidth := by
    dsimp [loadExp]
    unfold groupLoadExponent
    exact Nat.div_mul_le_self _ _
  have fieldBase : fieldExp * (12 * denominator) <= blockWidth := by
    dsimp [fieldExp]
    unfold stepFieldExponent stepDimension
    exact Nat.div_mul_le_self _ _
  have requestBase : requestExp * denominator <=
      numerator * stepInputWidth level blockWidth := by
    dsimp [requestExp]
    exact Nat.div_mul_le_self _ _
  have groupScaled : groupExp * (24 * denominator) <=
      12 * (groupNumerator * blockWidth) := by
    calc
      groupExp * (24 * denominator) =
          12 * (groupExp * (2 * denominator)) := by ring
      _ <= 12 * (groupNumerator * blockWidth) := by gcongr
  have twiceLoadScaled : (loadExp + loadExp) * (24 * denominator) <=
      12 * ((4 * denominator - 1) * blockWidth) := by
    calc
      (loadExp + loadExp) * (24 * denominator) =
          12 * (loadExp * (4 * denominator)) := by ring
      _ <= 12 * ((4 * denominator - 1) * blockWidth) := by gcongr
  have fieldScaled : fieldExp * (24 * denominator) <=
      2 * blockWidth := by
    calc
      fieldExp * (24 * denominator) =
          2 * (fieldExp * (12 * denominator)) := by ring
      _ <= 2 * blockWidth := by gcongr
  have requestScaled : requestExp * (24 * denominator) <=
      24 * (numerator * stepInputWidth level blockWidth) := by
    calc
      requestExp * (24 * denominator) =
          24 * (requestExp * denominator) := by ring
      _ <= 24 * (numerator * stepInputWidth level blockWidth) := by gcongr
  have groupStep := groupRateNumerator_add_one level denominator
    levelAtLeastTwo denominatorPositive
  have fourStep : 4 * denominator - 1 + 1 = 4 * denominator :=
    Nat.sub_add_cancel (by omega)
  have levelDecomposition : level + 1 = (level - 1) + 2 := by omega
  have targetCoefficientIdentity :
      24 * denominator * (level + 1) =
        12 * (2 * denominator * (level - 1)) +
          12 * (4 * denominator) := by
    rw [levelDecomposition]
    ring
  have schedulerCoefficient :
      12 * groupNumerator + 12 * (4 * denominator - 1) + 3 <=
        24 * denominator * (level + 1) := by
    omega
  have schedulerMargin :
      (groupExp + loadExp + loadExp + fieldExp) *
          (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth := by
    calc
      (groupExp + loadExp + loadExp + fieldExp) *
            (24 * denominator) + blockWidth =
          groupExp * (24 * denominator) +
            (loadExp + loadExp) * (24 * denominator) +
            fieldExp * (24 * denominator) + blockWidth := by ring
      _ <= 12 * (groupNumerator * blockWidth) +
          12 * ((4 * denominator - 1) * blockWidth) +
          2 * blockWidth + blockWidth :=
        Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add groupScaled twiceLoadScaled) fieldScaled)
          le_rfl
      _ = (12 * groupNumerator +
          12 * (4 * denominator - 1) + 3) * blockWidth := by ring
      _ <= 24 * denominator * (level + 1) * blockWidth := by gcongr
  have schedulerBound := exponent_le_stepCommonExponent level denominator
    blockWidth (groupExp + loadExp + loadExp + fieldExp)
    denominatorPositive schedulerMargin
  have groupLineBound : groupExp + loadExp + fieldExp <=
      stepCommonExponent level denominator blockWidth := by
    exact (show groupExp + loadExp + fieldExp <=
        groupExp + loadExp + loadExp + fieldExp by omega).trans
      schedulerBound
  have targetStep : (level + 1) * numerator + 1 <=
      level * denominator := by omega
  have targetScaled := Nat.mul_le_mul_left 24 targetStep
  have requestCoefficient :
      24 * ((level + 1) * numerator) + 3 <=
        24 * denominator * (level + 1) := by
    calc
      24 * ((level + 1) * numerator) + 3 <=
          24 * ((level + 1) * numerator) + 24 := by omega
      _ = 24 * ((level + 1) * numerator + 1) := by ring
      _ <= 24 * (level * denominator) := targetScaled
      _ <= 24 * ((level + 1) * denominator) := by
        gcongr
        exact Nat.le_succ level
      _ = 24 * denominator * (level + 1) := by ring
  have requestMargin :
      (requestExp + fieldExp) * (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth := by
    calc
      (requestExp + fieldExp) * (24 * denominator) + blockWidth =
          requestExp * (24 * denominator) +
            fieldExp * (24 * denominator) + blockWidth := by ring
      _ <= 24 * (numerator * stepInputWidth level blockWidth) +
          2 * blockWidth + blockWidth :=
        Nat.add_le_add
          (Nat.add_le_add requestScaled fieldScaled) le_rfl
      _ = (24 * ((level + 1) * numerator) + 3) * blockWidth := by
        unfold stepInputWidth
        ring
      _ <= 24 * denominator * (level + 1) * blockWidth := by gcongr
  have requestBound := exponent_le_stepCommonExponent level denominator
    blockWidth (requestExp + fieldExp) denominatorPositive requestMargin
  have groupCoefficient :
      12 * groupNumerator + 24 * denominator + 1 <=
        24 * denominator * (level + 1) := by
    omega
  have groupMargin :
      (groupExp + blockWidth) * (24 * denominator) + blockWidth <=
        24 * denominator * (level + 1) * blockWidth := by
    calc
      (groupExp + blockWidth) * (24 * denominator) + blockWidth =
          groupExp * (24 * denominator) +
            24 * denominator * blockWidth + blockWidth := by ring
      _ <= 12 * (groupNumerator * blockWidth) +
          24 * denominator * blockWidth + blockWidth := by gcongr
      _ = (12 * groupNumerator + 24 * denominator + 1) *
          blockWidth := by ring
      _ <= 24 * denominator * (level + 1) * blockWidth := by gcongr
  have groupBound := exponent_le_stepCommonExponent level denominator
    blockWidth (groupExp + blockWidth) denominatorPositive groupMargin
  exact ⟨schedulerBound, groupLineBound, requestBound, groupBound⟩

/-- Fixed multiplicative loss in the field-cardinality estimate. -/
def stepFieldConstant (denominator : Nat) : Nat :=
  2 ^ (4 * stepDimension denominator + 3)

/-- Fixed multiplicative loss in the affine resource-slot estimate. -/
def stepSlotConstant (denominator : Nat) : Nat :=
  2 ^ (stepDimension denominator *
    (4 * stepDimension denominator + 3))

/-- Common constant multiplying the strict live-volume exponential. -/
def stepVolumeConstant (denominator : Nat) : Nat :=
  9 * stepFieldConstant denominator + 4 * stepSlotConstant denominator

/-- The complete canonical live-record volume is a fixed constant times a
strict subunit exponential. -/
theorem step_overheadVolume_exponential_le
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator)) :
    let dimension := stepDimension denominator
    let dimensionPositive := stepDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let groups := groupCount level denominator blockWidth
    let schedulerDepth :=
      FiniteParameters.schedulerDepth copies groups width
    let routingDepth :=
      FiniteParameters.routingDepth copies groups dimension width
    OverheadBound.overheadVolume copies groups width schedulerDepth
        routingDepth <=
      stepVolumeConstant denominator *
        2 ^ stepCommonExponent level denominator blockWidth := by
  dsimp only
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let groupSize := requestGroupSize copies groups
  let groupExp := groupExponent level denominator blockWidth
  let loadExp := groupLoadExponent denominator blockWidth
  let fieldExp := stepFieldExponent denominator blockWidth
  let requestExp :=
    numerator * stepInputWidth level blockWidth / denominator
  let commonExp := stepCommonExponent level denominator blockWidth
  let fieldConstant := stepFieldConstant denominator
  let slotConstant := stepSlotConstant denominator
  have groupSizeBound : groupSize <= 2 ^ loadExp := by
    dsimp [groupSize, loadExp]
    exact requestGroupSize_le level numerator denominator blockWidth copies
      levelAtLeastTwo denominatorPositive rateBelowLevel blockLarge
      (by simpa [stepInputWidth, Nat.add_mul, Nat.add_comm] using copiesBound)
  have fieldBound : 2 ^ width <= fieldConstant * 2 ^ fieldExp := by
    have selected := fieldCard_le blockWidth dimension dimensionPositive
    dsimp [fieldConstant, fieldExp, stepFieldConstant, stepFieldExponent]
    exact selected
  have slotBound : 2 ^ (dimension * width) <=
      slotConstant * 2 ^ blockWidth := by
    have selected := fieldCard_pow_dimension_le blockWidth dimension
      dimensionPositive
    dsimp [slotConstant, stepSlotConstant]
    exact selected
  obtain ⟨schedulerExponent, groupLineExponent, incidenceExponent,
      slotExponent⟩ := step_volume_exponents_le level numerator denominator
        blockWidth levelAtLeastTwo denominatorPositive rateBelowLevel
  have groupsPower : groups = 2 ^ groupExp := by rfl
  have groupsBound : groups <= 2 ^ groupExp := groupsPower.le
  have schedulerPower :
      groups * groupSize * groupSize * 2 ^ width <=
        fieldConstant * 2 ^ commonExp := by
    calc
      groups * groupSize * groupSize * 2 ^ width <=
          2 ^ groupExp * 2 ^ loadExp * 2 ^ loadExp *
            (fieldConstant * 2 ^ fieldExp) := by
        gcongr
      _ = fieldConstant *
          2 ^ (groupExp + loadExp + loadExp + fieldExp) := by
        rw [Nat.pow_add, Nat.pow_add, Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) schedulerExponent)
  have groupLinePower : groups * groupSize * 2 ^ width <=
      fieldConstant * 2 ^ commonExp := by
    calc
      groups * groupSize * 2 ^ width <=
          2 ^ groupExp * 2 ^ loadExp *
            (fieldConstant * 2 ^ fieldExp) := by gcongr
      _ = fieldConstant * 2 ^ (groupExp + loadExp + fieldExp) := by
        rw [Nat.pow_add, Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) groupLineExponent)
  have incidencePower : copies * 2 ^ width <=
      fieldConstant * 2 ^ commonExp := by
    calc
      copies * 2 ^ width <=
          2 ^ requestExp * (fieldConstant * 2 ^ fieldExp) := by gcongr
      _ = fieldConstant * 2 ^ (requestExp + fieldExp) := by
        rw [Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) incidenceExponent)
  have slotsPower : groups * 2 ^ (dimension * width) <=
      slotConstant * 2 ^ commonExp := by
    calc
      groups * 2 ^ (dimension * width) <=
          2 ^ groupExp * (slotConstant * 2 ^ blockWidth) := by gcongr
      _ = slotConstant * 2 ^ (groupExp + blockWidth) := by
        rw [Nat.pow_add]
        ring
      _ <= slotConstant * 2 ^ commonExp :=
        Nat.mul_le_mul_left slotConstant
          (Nat.pow_le_pow_right (by omega) slotExponent)
  have rawVolume := step_overheadVolume_le level denominator blockWidth
    copies denominatorPositive copiesPositive
  calc
    OverheadBound.overheadVolume copies groups width
        (FiniteParameters.schedulerDepth copies groups width)
        (FiniteParameters.routingDepth copies groups dimension width) <=
      2 * groups * groupSize * groupSize * 2 ^ width +
        groups * groupSize * 2 ^ width +
        6 * copies * 2 ^ width +
        4 * groups * 2 ^ (dimension * width) := rawVolume
    _ <= 2 * (fieldConstant * 2 ^ commonExp) +
        fieldConstant * 2 ^ commonExp +
        6 * (fieldConstant * 2 ^ commonExp) +
        4 * (slotConstant * 2 ^ commonExp) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (show 2 * groups * groupSize * groupSize * 2 ^ width <=
                2 * (fieldConstant * 2 ^ commonExp) by
              calc
                2 * groups * groupSize * groupSize * 2 ^ width =
                    2 * (groups * groupSize * groupSize * 2 ^ width) := by
                  ring
                _ <= 2 * (fieldConstant * 2 ^ commonExp) :=
                  Nat.mul_le_mul_left 2 schedulerPower)
            groupLinePower)
          (show 6 * copies * 2 ^ width <=
              6 * (fieldConstant * 2 ^ commonExp) by
            calc
              6 * copies * 2 ^ width = 6 * (copies * 2 ^ width) := by ring
              _ <= 6 * (fieldConstant * 2 ^ commonExp) :=
                Nat.mul_le_mul_left 6 incidencePower))
        (show 4 * groups * 2 ^ (dimension * width) <=
            4 * (slotConstant * 2 ^ commonExp) by
          calc
            4 * groups * 2 ^ (dimension * width) =
                4 * (groups * 2 ^ (dimension * width)) := by ring
            _ <= 4 * (slotConstant * 2 ^ commonExp) :=
              Nat.mul_le_mul_left 4 slotsPower)
    _ = stepVolumeConstant denominator * 2 ^ commonExp := by
      unfold stepVolumeConstant
      dsimp [fieldConstant, slotConstant]
      ring

end BlockInduction
end MassProduction
end Algebraic
