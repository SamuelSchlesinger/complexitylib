/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BlockInductionParameters

/-!
# Finite ledger for one equal-block induction step

This module places every width and sorting depth used by one induction step
under a shared parameter bound and reduces the exact live-record volume to
four explicit contributions consumed by the exponent analysis.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BlockInduction

open CodeParameters
open GroupedScheduler
open LineEnumeration
open Sorting

/-! ## A shared bound for all finite bookkeeping parameters -/

/-- Width of the recursive suffix containing `level` equal blocks. -/
def stepSuffixWidth (level blockWidth : Nat) : Nat :=
  level * blockWidth

/-- Total width of the prefix block followed by the recursive suffix. -/
def stepInputWidth (level blockWidth : Nat) : Nat :=
  blockWidth + level * blockWidth

/-- Linear upper bound for the least admissible extension-field width. -/
def stepWidthBound
    (level denominator blockWidth : Nat) : Nat :=
  stepInputWidth level blockWidth + 4 * stepDimension denominator + 3

/-- Common bound for every width and sorting depth in the finite ledger. -/
def stepParameterBound
    (level denominator blockWidth : Nat) : Nat :=
  let inputWidth := stepInputWidth level blockWidth
  let widthBound := stepWidthBound level denominator blockWidth
  inputWidth + widthBound +
    stepDimension denominator * widthBound + 2

theorem targetNumerator_lt_denominator
    (level numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator) :
    numerator < denominator := by
  by_contra notBelow
  have denominatorLe : denominator <= numerator := by omega
  have scaled := Nat.mul_le_mul_left (level + 1) denominatorLe
  have strict : level * denominator < (level + 1) * denominator := by
    calc
      level * denominator < level * denominator + denominator := by omega
      _ = (level + 1) * denominator := by ring
  exact (rateBelowLevel.trans_le
    (show level * denominator <= (level + 1) * numerator from
      strict.le.trans scaled)).false

theorem groupExponent_le_inputWidth
    (level denominator blockWidth : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator) :
    groupExponent level denominator blockWidth <=
      stepInputWidth level blockWidth := by
  have numeratorStep := groupRateNumerator_add_one level denominator
    levelAtLeastTwo denominatorPositive
  apply Nat.div_le_of_le_mul
  unfold groupRateDenominator stepInputWidth
  have coefficientBound :
      groupRateNumerator level denominator <=
        2 * denominator * (level + 1) := by
    calc
      groupRateNumerator level denominator <=
          groupRateNumerator level denominator + 1 := Nat.le_succ _
      _ = 2 * denominator * (level - 1) := numeratorStep
      _ <= 2 * denominator * (level + 1) :=
        Nat.mul_le_mul_left (2 * denominator) (by omega)
  calc
    groupRateNumerator level denominator * blockWidth <=
        (2 * denominator * (level + 1)) * blockWidth := by gcongr
    _ = (2 * denominator) * stepInputWidth level blockWidth := by
      unfold stepInputWidth
      ring

theorem requestGroupSize_le_copies
    (copies groups : Nat)
    (groupsPositive : 0 < groups) :
    requestGroupSize copies groups <= copies := by
  apply (ceilDiv_le_iff_le_mul groupsPositive).2
  calc
    copies = 1 * copies := by ring
    _ <= groups * copies :=
      Nat.mul_le_mul_right copies (by omega)

/-- Every bit width and network depth in one induction-step ledger is bounded
by one explicit expression linear in the total input width. -/
theorem step_parameters_bounded
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator)) :
    let dimension := stepDimension denominator
    let dimensionPositive := stepDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let groups := groupCount level denominator blockWidth
    let schedulerDepth :=
      FiniteParameters.schedulerDepth copies groups width
    let groupBitWidth := FiniteParameters.groupBitWidth groups
    let orderWidth := FiniteParameters.orderWidth copies width
    let routingDepth :=
      FiniteParameters.routingDepth copies groups dimension width
    let bound := stepParameterBound level denominator blockWidth
    dimension <= bound ∧
      width <= bound ∧
      schedulerDepth <= bound ∧
      blockWidth <= bound ∧
      IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
        bound ∧
      stepSuffixWidth level blockWidth <= bound ∧
      orderWidth + 1 <= bound ∧
      routingDepth <= bound := by
  dsimp only
  let inputWidth := stepInputWidth level blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let widthBound := stepWidthBound level denominator blockWidth
  let schedulerDepth := FiniteParameters.schedulerDepth copies groups width
  let groupBitWidth := FiniteParameters.groupBitWidth groups
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth :=
    FiniteParameters.routingDepth copies groups dimension width
  let bound := stepParameterBound level denominator blockWidth
  have inputWidthEq : inputWidth = (level + 1) * blockWidth := by
    dsimp [inputWidth, stepInputWidth]
    ring
  have suffixWidthEq : suffixWidth = level * blockWidth := rfl
  have widthSelected : width <= widthBound := by
    have selected := fieldWidth_le_quotient_add blockWidth dimension
      dimensionPositive
    dsimp [widthBound, stepWidthBound, inputWidth, stepInputWidth]
    exact selected.trans <| by
      have quotient := Nat.div_le_self blockWidth dimension
      have blockLe : blockWidth <= (level + 1) * blockWidth := by
        calc
          blockWidth = 1 * blockWidth := by ring
          _ <= (level + 1) * blockWidth :=
            Nat.mul_le_mul_right blockWidth (by omega)
      omega
  have numeratorBelow : numerator <= denominator :=
    (targetNumerator_lt_denominator level numerator denominator
      denominatorPositive rateBelowLevel).le
  have requestExponentLeInput :
      numerator * inputWidth / denominator <= inputWidth := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right inputWidth numeratorBelow
  have copiesCoarse : copies <= 2 ^ inputWidth :=
    copiesBound.trans (Nat.pow_le_pow_right (by omega)
      requestExponentLeInput)
  have groupExponentBound :
      groupExponent level denominator blockWidth <= inputWidth := by
    exact groupExponent_le_inputWidth level denominator blockWidth
      levelAtLeastTwo denominatorPositive
  have groupsCoarse : groups <= 2 ^ inputWidth := by
    dsimp [groups, groupCount]
    exact Nat.pow_le_pow_right (by omega) groupExponentBound
  have widthPositive := fieldWidth_positive blockWidth dimension
    dimensionPositive
  have scalarBound : nonzeroScalarCount width <= 2 ^ width := by
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    exact Nat.sub_le _ _
  have widthPowerBound : 2 ^ width <= 2 ^ widthBound :=
    Nat.pow_le_pow_right (by omega) widthSelected
  have incidenceBound :
      FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound) := by
    unfold FiniteParameters.incidenceCount
    calc
      copies * nonzeroScalarCount width <=
          2 ^ inputWidth * 2 ^ width := Nat.mul_le_mul copiesCoarse scalarBound
      _ <= 2 ^ inputWidth * 2 ^ widthBound := by gcongr
      _ = 2 ^ (inputWidth + widthBound) :=
        (Nat.pow_add _ _ _).symm
  have groupSizeBound : requestGroupSize copies groups <= copies :=
    requestGroupSize_le_copies copies groups <| by
      dsimp [groups]
      exact groupCount_positive level denominator blockWidth
  have schedulerRecordBound :
      requestGroupSize copies groups * nonzeroScalarCount width <=
        2 ^ (inputWidth + widthBound) := by
    calc
      requestGroupSize copies groups * nonzeroScalarCount width <=
          copies * nonzeroScalarCount width := by gcongr
      _ = FiniteParameters.incidenceCount copies width := rfl
      _ <= 2 ^ (inputWidth + widthBound) := incidenceBound
  have schedulerDepthBound : schedulerDepth <= inputWidth + widthBound := by
    unfold schedulerDepth FiniteParameters.schedulerDepth
    exact FiniteParameters.binaryDepth_le _ _ schedulerRecordBound
  have orderDepthBound : orderWidth <= inputWidth + widthBound := by
    unfold orderWidth FiniteParameters.orderWidth
    exact FiniteParameters.binaryDepth_le _ _ incidenceBound
  have groupWidthBound : groupBitWidth <= inputWidth := by
    unfold groupBitWidth FiniteParameters.groupBitWidth
    exact FiniteParameters.binaryDepth_le _ _ groupsCoarse
  have slotBound :
      FiniteParameters.resourceSlotCount groups dimension width <=
        2 ^ (inputWidth + dimension * widthBound) := by
    unfold FiniteParameters.resourceSlotCount
    exact Nat.pow_le_pow_right (by omega) <| by
      exact Nat.add_le_add groupWidthBound
        (Nat.mul_le_mul_left dimension widthSelected)
  let routingExponent := inputWidth + widthBound +
    dimension * widthBound + 1
  have routingRecordBound :
      FiniteParameters.routingRecords copies groups dimension width <=
        2 ^ routingExponent := by
    have incidenceRaised : FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      incidenceBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have slotsRaised :
        FiniteParameters.resourceSlotCount groups dimension width <=
          2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      slotBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    unfold FiniteParameters.routingRecords
    calc
      FiniteParameters.incidenceCount copies width +
          FiniteParameters.resourceSlotCount groups dimension width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) +
          2 ^ (inputWidth + widthBound + dimension * widthBound) :=
        Nat.add_le_add incidenceRaised slotsRaised
      _ = 2 ^ routingExponent := by
        rw [show routingExponent =
          (inputWidth + widthBound + dimension * widthBound) + 1 by rfl,
          Nat.pow_succ]
        ring
  have routingDepthBound : routingDepth <= routingExponent := by
    unfold routingDepth FiniteParameters.routingDepth
    exact FiniteParameters.binaryDepth_le _ _ routingRecordBound
  have boundEq : bound =
      inputWidth + widthBound + dimension * widthBound + 2 := by rfl
  have dimensionLeWidthBound : dimension <= widthBound := by
    dsimp [widthBound, stepWidthBound]
    omega
  have inputLeBound : inputWidth <= bound := by rw [boundEq]; omega
  have widthBoundLeBound : widthBound <= bound := by rw [boundEq]; omega
  have suffixLeInput : suffixWidth <= inputWidth := by
    dsimp [suffixWidth, inputWidth, stepSuffixWidth, stepInputWidth]
    omega
  have schedulerBound : schedulerDepth <= bound :=
    schedulerDepthBound.trans (by rw [boundEq]; omega)
  have blockLeInput : blockWidth <= inputWidth := by
    dsimp [inputWidth, stepInputWidth]
    omega
  have keyBound : IncidenceRouting.incidenceKeyWidth
      groupBitWidth dimension width <= bound := by
    unfold IncidenceRouting.incidenceKeyWidth
    have productBound : dimension * width <= dimension * widthBound :=
      Nat.mul_le_mul_left dimension widthSelected
    rw [boundEq]
    omega
  have orderBound : orderWidth + 1 <= bound :=
    (Nat.add_le_add_right orderDepthBound 1).trans
      (by rw [boundEq]; omega)
  have routingExponentLeBound : routingExponent <= bound := by
    rw [boundEq]
    dsimp [routingExponent]
    omega
  have localBounds :
      dimension <= bound ∧ width <= bound ∧ schedulerDepth <= bound ∧
        blockWidth <= bound ∧
        IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
          bound ∧ suffixWidth <= bound ∧ orderWidth + 1 <= bound ∧
        routingDepth <= bound :=
    ⟨dimensionLeWidthBound.trans widthBoundLeBound,
      widthSelected.trans widthBoundLeBound, schedulerBound,
      blockLeInput.trans inputLeBound, keyBound,
      suffixLeInput.trans inputLeBound, orderBound,
      routingDepthBound.trans routingExponentLeBound⟩
  simpa only [inputWidth, suffixWidth, dimension, dimensionPositive, width,
    groups, schedulerDepth, groupBitWidth, orderWidth, routingDepth, bound]
    using localBounds

/-! ## Exact live-record volume -/

/-- The canonical live-record volume has precisely the four contributions
needed by the exponent calculation: grouped scheduling, group-line work,
incidences, and group-indexed resource slots. -/
theorem step_overheadVolume_le
    (level denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (copiesPositive : 0 < copies) :
    let dimension := stepDimension denominator
    let dimensionPositive := stepDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let groups := groupCount level denominator blockWidth
    let groupSize := requestGroupSize copies groups
    OverheadBound.overheadVolume copies groups width
        (FiniteParameters.schedulerDepth copies groups width)
        (FiniteParameters.routingDepth copies groups dimension width) <=
      2 * groups * groupSize * groupSize * 2 ^ width +
        groups * groupSize * 2 ^ width +
        6 * copies * 2 ^ width +
        4 * groups * 2 ^ (dimension * width) := by
  dsimp only
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let groupSize := requestGroupSize copies groups
  let scalarCount := nonzeroScalarCount width
  let schedulerRecords := groupSize * scalarCount
  let routingRecords :=
    FiniteParameters.routingRecords copies groups dimension width
  have widthPositive := fieldWidth_positive blockWidth dimension
    dimensionPositive
  have groupsPositive : 0 < groups := by
    dsimp [groups]
    exact groupCount_positive level denominator blockWidth
  have groupSizePositive : 0 < groupSize := by
    by_contra notPositive
    have groupSizeZero : groupSize = 0 := by omega
    have impossible := (ceilDiv_le_iff_le_mul groupsPositive).mp
      (show requestGroupSize copies groups <= 0 by
        simpa only [groupSize] using Nat.le_of_eq groupSizeZero)
    omega
  have scalarPositive : 0 < scalarCount := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    have : 1 < 2 ^ width :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 widthPositive
    exact Nat.sub_pos_of_lt this
  have schedulerRecordsPositive : 0 < schedulerRecords :=
    Nat.mul_pos groupSizePositive scalarPositive
  have schedulerNetwork :
      networkRecords
          (FiniteParameters.schedulerDepth copies groups width) <=
        2 * (groupSize * scalarCount) := by
    exact Nat.le_of_lt <| by
      simpa [FiniteParameters.schedulerDepth, groupSize, schedulerRecords]
        using FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          schedulerRecords schedulerRecordsPositive
  have scalarBound : scalarCount <= 2 ^ width := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    exact Nat.sub_le _ _
  have groupWidthBound :
      FiniteParameters.groupBitWidth groups <=
        groupExponent level denominator blockWidth := by
    unfold FiniteParameters.groupBitWidth
    apply FiniteParameters.binaryDepth_le
    dsimp [groups]
    unfold groupCount
    exact le_rfl
  have slotBound :
      FiniteParameters.resourceSlotCount groups dimension width <=
        groups * 2 ^ (dimension * width) := by
    unfold FiniteParameters.resourceSlotCount
    calc
      2 ^ (FiniteParameters.groupBitWidth groups + dimension * width) <=
          2 ^ (groupExponent level denominator blockWidth +
            dimension * width) :=
        Nat.pow_le_pow_right (by omega)
          (Nat.add_le_add_right groupWidthBound _)
      _ = groups * 2 ^ (dimension * width) := by
        rw [Nat.pow_add]
        dsimp [groups]
        unfold groupCount
        rfl
  have routingRecordsPositive : 0 < routingRecords := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords
    have slotPositive : 0 <
        FiniteParameters.resourceSlotCount groups dimension width := by
      unfold FiniteParameters.resourceSlotCount
      positivity
    omega
  have routingNetwork :
      networkRecords
          (FiniteParameters.routingDepth copies groups dimension width) <=
        2 * routingRecords := by
    exact Nat.le_of_lt <| by
      simpa [FiniteParameters.routingDepth, routingRecords]
        using FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          routingRecords routingRecordsPositive
  have routingRecordsBound : routingRecords <=
      copies * 2 ^ width + groups * 2 ^ (dimension * width) := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords FiniteParameters.incidenceCount
    exact Nat.add_le_add
      (Nat.mul_le_mul_left copies scalarBound) slotBound
  unfold OverheadBound.overheadVolume
  dsimp only [groupSize]
  calc
    groups * requestGroupSize copies groups *
          (networkRecords
              (FiniteParameters.schedulerDepth copies groups width) +
            2 ^ width) +
        2 * (copies * 2 ^ width) +
        2 * networkRecords
          (FiniteParameters.routingDepth copies groups dimension width) <=
      groups * groupSize *
          (2 * (groupSize * scalarCount) + 2 ^ width) +
        2 * (copies * 2 ^ width) + 2 * (2 * routingRecords) := by
      gcongr
    _ <= groups * groupSize *
          (2 * (groupSize * 2 ^ width) + 2 ^ width) +
        2 * (copies * 2 ^ width) +
          2 * (2 * (copies * 2 ^ width +
            groups * 2 ^ (dimension * width))) := by
      gcongr
    _ = 2 * groups * groupSize * groupSize * 2 ^ width +
        groups * groupSize * 2 ^ width +
        6 * copies * 2 ^ width +
        4 * groups * 2 ^ (dimension * width) := by ring

end BlockInduction
end MassProduction
end Algebraic
