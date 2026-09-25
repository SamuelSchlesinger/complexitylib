/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.EqualBlockParameters
public import Complexitylib.Algebraic.MassProduction.OverheadBound

/-!
# Finite ledger for the two-block base case

This module bounds every width and sorting depth in the canonical two-block
construction by one shared parameter and reduces its exact live-record
volume to three explicit contributions.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters
open GroupedScheduler
open LineEnumeration
open Sorting

/-- Linear upper bound for the selected extension-field bit width in the
two-block construction. -/
def twoBlockWidthBound (denominator blockWidth : Nat) : Nat :=
  blockWidth + 4 * twoBlockDimension denominator + 3

/-- Shared linear bound for every bit width and sorting depth occurring in
the canonical two-block ledger. -/
def twoBlockParameterBound (denominator blockWidth : Nat) : Nat :=
  let dimension := twoBlockDimension denominator
  let widthBound := twoBlockWidthBound denominator blockWidth
  (blockWidth + blockWidth) + widthBound + dimension * widthBound + 2

theorem twoBlock_fieldWidth_le_widthBound
    (denominator blockWidth : Nat)
    (denominatorPositive : 0 < denominator) :
    fieldWidth blockWidth (twoBlockDimension denominator)
        (twoBlockDimension_positive denominatorPositive) <=
      twoBlockWidthBound denominator blockWidth := by
  have selected := fieldWidth_le_quotient_add blockWidth
    (twoBlockDimension denominator)
    (twoBlockDimension_positive denominatorPositive)
  unfold twoBlockWidthBound
  exact selected.trans (by
    have := Nat.div_le_self blockWidth (twoBlockDimension denominator)
    omega)

/-- All coefficient parameters in the canonical two-block ledger lie below
`twoBlockParameterBound`. -/
theorem twoBlock_parameters_bounded
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator)) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
    let groupBitWidth := FiniteParameters.groupBitWidth 1
    let orderWidth := FiniteParameters.orderWidth copies width
    let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
    let bound := twoBlockParameterBound denominator blockWidth
    dimension <= bound ∧
      width <= bound ∧
      schedulerDepth <= bound ∧
      blockWidth <= bound ∧
      IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
        bound ∧
      blockWidth <= bound ∧
      orderWidth + 1 <= bound ∧
      routingDepth <= bound := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let widthBound := twoBlockWidthBound denominator blockWidth
  let inputWidth := blockWidth + blockWidth
  let exponent := numerator * inputWidth / denominator
  let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
  let groupBitWidth := FiniteParameters.groupBitWidth 1
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
  let bound := twoBlockParameterBound denominator blockWidth
  have dimensionPositive' : 0 < dimension := dimensionPositive
  have widthSelected : width <= widthBound := by
    exact twoBlock_fieldWidth_le_widthBound denominator blockWidth
      denominatorPositive
  have numeratorBelow : numerator <= denominator := by omega
  have exponentLeInput : exponent <= inputWidth := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right inputWidth numeratorBelow
  have copiesCoarse : copies <= 2 ^ inputWidth :=
    copiesBound.trans (Nat.pow_le_pow_right (by omega) exponentLeInput)
  have scalarBound : nonzeroScalarCount width <= 2 ^ width := by
    rw [nonzeroScalarCount_eq_two_pow_sub_one
      (fieldWidth_positive blockWidth dimension dimensionPositive)]
    exact Nat.sub_le _ _
  have widthPowerBound : 2 ^ width <= 2 ^ widthBound :=
    Nat.pow_le_pow_right (by omega) widthSelected
  have incidenceBound :
      FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound) := by
    unfold FiniteParameters.incidenceCount
    calc
      copies * nonzeroScalarCount width <= 2 ^ inputWidth * 2 ^ width :=
        Nat.mul_le_mul copiesCoarse scalarBound
      _ <= 2 ^ inputWidth * 2 ^ widthBound := by gcongr
      _ = 2 ^ (inputWidth + widthBound) :=
        (Nat.pow_add _ _ _).symm
  have schedulerRecordBound :
      requestGroupSize copies 1 * nonzeroScalarCount width <=
        2 ^ (inputWidth + widthBound) := by
    simpa [requestGroupSize, FiniteParameters.incidenceCount] using
      incidenceBound
  have schedulerDepthBound : schedulerDepth <= inputWidth + widthBound := by
    unfold schedulerDepth FiniteParameters.schedulerDepth
    exact FiniteParameters.binaryDepth_le _ _ schedulerRecordBound
  have orderDepthBound : orderWidth <= inputWidth + widthBound := by
    unfold orderWidth FiniteParameters.orderWidth
    exact FiniteParameters.binaryDepth_le _ _ incidenceBound
  have slotBound : FiniteParameters.resourceSlotCount 1 dimension width <=
      2 ^ (dimension * widthBound) := by
    unfold FiniteParameters.resourceSlotCount
      FiniteParameters.groupBitWidth FiniteParameters.binaryDepth
    simp only [Nat.clog_one_right, zero_add]
    exact Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left dimension widthSelected)
  let routingExponent := inputWidth + widthBound + dimension * widthBound + 1
  have routingRecordBound :
      FiniteParameters.routingRecords copies 1 dimension width <=
        2 ^ routingExponent := by
    have incidenceRaised : FiniteParameters.incidenceCount copies width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      incidenceBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have slotsRaised : FiniteParameters.resourceSlotCount 1 dimension width <=
        2 ^ (inputWidth + widthBound + dimension * widthBound) :=
      slotBound.trans (Nat.pow_le_pow_right (by omega) (by omega))
    unfold FiniteParameters.routingRecords
    calc
      FiniteParameters.incidenceCount copies width +
          FiniteParameters.resourceSlotCount 1 dimension width <=
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
    dsimp [widthBound]
    unfold twoBlockWidthBound
    omega
  have inputLeBound : inputWidth <= bound := by
    rw [boundEq]
    omega
  have widthBoundLeBound : widthBound <= bound := by
    rw [boundEq]
    omega
  have productLeBound : dimension * widthBound <= bound := by
    rw [boundEq]
    omega
  have routingExponentLeBound : routingExponent <= bound := by
    rw [boundEq]
    dsimp [routingExponent]
    omega
  have schedulerBound : schedulerDepth <= bound :=
    schedulerDepthBound.trans (by rw [boundEq]; omega)
  have blockBound : blockWidth <= bound := by
    exact (by omega : blockWidth <= inputWidth).trans inputLeBound
  have keyBound : IncidenceRouting.incidenceKeyWidth
      groupBitWidth dimension width <= bound := by
    have productBound : dimension * width <= dimension * widthBound :=
      Nat.mul_le_mul_left dimension widthSelected
    have productPlusBound : dimension * width + 1 <= bound :=
      (Nat.add_le_add_right productBound 1).trans (by rw [boundEq]; omega)
    dsimp [groupBitWidth, FiniteParameters.groupBitWidth,
      FiniteParameters.binaryDepth, IncidenceRouting.incidenceKeyWidth]
    simpa using productPlusBound
  have orderBound : orderWidth + 1 <= bound :=
    (Nat.add_le_add_right orderDepthBound 1).trans (by rw [boundEq]; omega)
  have localBounds :
      dimension <= bound ∧
        width <= bound ∧
        schedulerDepth <= bound ∧
        blockWidth <= bound ∧
        IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width <=
          bound ∧
        blockWidth <= bound ∧
        orderWidth + 1 <= bound ∧
        routingDepth <= bound :=
    ⟨dimensionLeWidthBound.trans widthBoundLeBound,
      widthSelected.trans widthBoundLeBound, schedulerBound, blockBound,
      keyBound, blockBound, orderBound,
      routingDepthBound.trans routingExponentLeBound⟩
  simpa only [dimension, dimensionPositive, width, schedulerDepth,
    groupBitWidth, orderWidth, routingDepth, bound] using localBounds

/-- The exact canonical record volume in the two-block case has the three
expected contributions: quadratic scheduling, incidences, and resource
slots. -/
theorem twoBlock_overheadVolume_le
    (denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (copiesPositive : 0 < copies) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    OverheadBound.overheadVolume copies 1 width
        (FiniteParameters.schedulerDepth copies 1 width)
        (FiniteParameters.routingDepth copies 1 dimension width) <=
      2 * copies * copies * 2 ^ width +
        7 * copies * 2 ^ width +
        4 * 2 ^ (dimension * width) := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let scalarCount := nonzeroScalarCount width
  let schedulerRecords := copies * scalarCount
  let routingRecords := FiniteParameters.routingRecords copies 1 dimension width
  have widthPositive := fieldWidth_positive blockWidth dimension
    dimensionPositive
  have scalarPositive : 0 < scalarCount := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    have : 1 < 2 ^ width := by
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).2 widthPositive
    exact Nat.sub_pos_of_lt this
  have schedulerRecordsPositive : 0 < schedulerRecords :=
    Nat.mul_pos copiesPositive scalarPositive
  have schedulerNetwork :
      networkRecords (FiniteParameters.schedulerDepth copies 1 width) <=
        2 * (copies * scalarCount) := by
    exact Nat.le_of_lt (by
      simpa [FiniteParameters.schedulerDepth, requestGroupSize,
        schedulerRecords] using
        FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          schedulerRecords schedulerRecordsPositive)
  have scalarBound : scalarCount <= 2 ^ width := by
    dsimp [scalarCount]
    rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
    exact Nat.sub_le _ _
  have slotEquality :
      FiniteParameters.resourceSlotCount 1 dimension width =
        2 ^ (dimension * width) := by
    unfold FiniteParameters.resourceSlotCount
      FiniteParameters.groupBitWidth FiniteParameters.binaryDepth
    simp
  have routingRecordsPositive : 0 < routingRecords := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords
    rw [slotEquality]
    positivity
  have routingNetwork :
      networkRecords
          (FiniteParameters.routingDepth copies 1 dimension width) <=
        2 * routingRecords := by
    exact Nat.le_of_lt (by
      simpa [FiniteParameters.routingDepth, routingRecords] using
        FiniteParameters.networkRecords_binaryDepth_lt_two_mul
          routingRecords routingRecordsPositive)
  have routingRecordsBound : routingRecords <=
      copies * 2 ^ width + 2 ^ (dimension * width) := by
    dsimp [routingRecords]
    unfold FiniteParameters.routingRecords FiniteParameters.incidenceCount
    rw [slotEquality]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left copies scalarBound) _
  unfold OverheadBound.overheadVolume
  simp only [requestGroupSize, ceilDiv_one, one_mul]
  calc
    copies *
          (networkRecords (FiniteParameters.schedulerDepth copies 1 width) +
            2 ^ width) +
        2 * (copies * 2 ^ width) +
        2 * networkRecords
          (FiniteParameters.routingDepth copies 1 dimension width) <=
      copies * (2 * (copies * scalarCount) + 2 ^ width) +
        2 * (copies * 2 ^ width) + 2 * (2 * routingRecords) := by
      gcongr
    _ <= copies * (2 * (copies * 2 ^ width) + 2 ^ width) +
        2 * (copies * 2 ^ width) +
        2 * (2 * (copies * 2 ^ width +
          2 ^ (dimension * width))) := by
      gcongr
    _ = 2 * copies * copies * 2 ^ width +
        7 * copies * 2 ^ width +
        4 * 2 ^ (dimension * width) := by ring

end EqualBlock
end MassProduction
end Algebraic
