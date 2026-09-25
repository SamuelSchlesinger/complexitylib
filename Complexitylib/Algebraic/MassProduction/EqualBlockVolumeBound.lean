/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.EqualBlockLedger
public import Complexitylib.Algebraic.MassProduction.Growth
public import Complexitylib.Algebraic.MassProduction.OverheadBound

/-!
# Exponential live-volume bound for the two-block base case

This module places the canonical two-block record volume below one binary
exponential with a fixed strict margin from the complete input width. Its
endpoint is `twoBlock_overheadVolume_exponential_le`.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters

/-- Denominator used for the common strict subunit exponent in the two-block
overhead bound. -/
def twoBlockMarginDenominator (denominator : Nat) : Nat :=
  6 * denominator

/-- Fixed multiplicative loss in the field-cardinality upper bound. -/
def twoBlockFieldConstant (denominator : Nat) : Nat :=
  2 ^ (4 * twoBlockDimension denominator + 3)

/-- Fixed multiplicative loss after raising the field cardinality to the code
dimension. -/
def twoBlockSlotConstant (denominator : Nat) : Nat :=
  2 ^ (twoBlockDimension denominator *
    (4 * twoBlockDimension denominator + 3))

/-- Fixed coefficient for the complete canonical record-volume bound. -/
def twoBlockVolumeConstant (denominator : Nat) : Nat :=
  9 * twoBlockFieldConstant denominator +
    4 * twoBlockSlotConstant denominator

/-- Slope relating every concrete ledger width to the full two-block input
length. -/
def twoBlockParameterSlope (denominator : Nat) : Nat :=
  let dimension := twoBlockDimension denominator
  3 + (dimension + 1) * (4 * dimension + 4)

/-- Constant coefficient of the degree-ten common ledger envelope. -/
def twoBlockCoefficientConstant (denominator : Nat) : Nat :=
  let slope := twoBlockParameterSlope denominator
  1000000 * (slope + 1) ^ 10 + 5 * slope

theorem twoBlock_parameterBound_le
    (denominator blockWidth : Nat) :
    twoBlockParameterBound denominator blockWidth <=
      twoBlockParameterSlope denominator *
        (blockWidth + blockWidth + 1) := by
  let dimension := twoBlockDimension denominator
  let inputWidth := blockWidth + blockWidth
  let widthBound := twoBlockWidthBound denominator blockWidth
  let slope := twoBlockParameterSlope denominator
  have blockLeInput : blockWidth <= inputWidth := by
    dsimp [inputWidth]
    omega
  have widthLinear : widthBound <=
      (4 * dimension + 4) * (inputWidth + 1) := by
    dsimp [widthBound]
    unfold twoBlockWidthBound
    change blockWidth + 4 * dimension + 3 <= _
    ring_nf
    omega
  change inputWidth + widthBound + dimension * widthBound + 2 <=
    slope * (inputWidth + 1)
  calc
    inputWidth + widthBound + dimension * widthBound + 2 =
        inputWidth + (dimension + 1) * widthBound + 2 := by ring
    _ <= inputWidth +
        (dimension + 1) * ((4 * dimension + 4) * (inputWidth + 1)) +
          2 := by gcongr
    _ <= slope * (inputWidth + 1) := by
      rw [show slope =
        3 + (dimension + 1) * (4 * dimension + 4) by rfl]
      ring_nf
      omega

/-- The common coefficient in the two-block ledger is a fixed constant times
a degree-ten polynomial in the complete input length. -/
theorem twoBlock_coefficient_le
    (denominator blockWidth : Nat) :
    let parameterBound := twoBlockParameterBound denominator blockWidth
    let inputWidth := blockWidth + blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      twoBlockCoefficientConstant denominator * (inputWidth + 1) ^ 10 := by
  dsimp only
  let parameterBound := twoBlockParameterBound denominator blockWidth
  let inputWidth := blockWidth + blockWidth
  let slope := twoBlockParameterSlope denominator
  have parameterLinear : parameterBound <= slope * (inputWidth + 1) :=
    twoBlock_parameterBound_le denominator blockWidth
  have successorLinear : parameterBound + 1 <=
      (slope + 1) * (inputWidth + 1) := by
    calc
      parameterBound + 1 <= slope * (inputWidth + 1) + 1 := by omega
      _ <= slope * (inputWidth + 1) + (inputWidth + 1) := by omega
      _ = (slope + 1) * (inputWidth + 1) := by ring
  have envelope := OverheadBound.coefficientEnvelope_le parameterBound
  have envelopePolynomial : OverheadBound.coefficientEnvelope parameterBound <=
      (1000000 * (slope + 1) ^ 10) * (inputWidth + 1) ^ 10 := by
    calc
      OverheadBound.coefficientEnvelope parameterBound <=
          1000000 * (parameterBound + 1) ^ 10 := envelope
      _ <= 1000000 * ((slope + 1) * (inputWidth + 1)) ^ 10 := by
        gcongr
      _ = (1000000 * (slope + 1) ^ 10) *
          (inputWidth + 1) ^ 10 := by
        rw [mul_pow]
        ring
  have inputPower : inputWidth + 1 <= (inputWidth + 1) ^ 10 := by
    calc
      inputWidth + 1 = (inputWidth + 1) * 1 := by omega
      _ <= (inputWidth + 1) * (inputWidth + 1) ^ 9 := by
        gcongr
        exact Nat.one_le_pow 9 (inputWidth + 1) (by omega)
      _ = (inputWidth + 1) ^ 10 := by
        rw [show 10 = 1 + 9 by omega, pow_add, pow_one]
  have linearPolynomial : 5 * parameterBound <=
      (5 * slope) * (inputWidth + 1) ^ 10 := by
    calc
      5 * parameterBound <= 5 * (slope * (inputWidth + 1)) := by gcongr
      _ <= 5 * (slope * (inputWidth + 1) ^ 10) := by gcongr
      _ = (5 * slope) * (inputWidth + 1) ^ 10 := by ring
  calc
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
        (1000000 * (slope + 1) ^ 10) * (inputWidth + 1) ^ 10 +
          (5 * slope) * (inputWidth + 1) ^ 10 :=
      Nat.add_le_add envelopePolynomial linearPolynomial
    _ = twoBlockCoefficientConstant denominator *
        (inputWidth + 1) ^ 10 := by
      unfold twoBlockCoefficientConstant
      dsimp [slope]
      ring

theorem twoBlock_coefficient_le_monomial
    (denominator blockWidth : Nat)
    (blockPositive : 0 < blockWidth) :
    let parameterBound := twoBlockParameterBound denominator blockWidth
    let inputWidth := blockWidth + blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      (twoBlockCoefficientConstant denominator * 2 ^ 10) *
        inputWidth ^ 10 := by
  dsimp only
  let inputWidth := blockWidth + blockWidth
  have inputPositive : 0 < inputWidth := by dsimp [inputWidth]; omega
  have successorBound : inputWidth + 1 <= 2 * inputWidth := by omega
  exact (twoBlock_coefficient_le denominator blockWidth).trans <| by
    calc
      twoBlockCoefficientConstant denominator * (inputWidth + 1) ^ 10 <=
          twoBlockCoefficientConstant denominator * (2 * inputWidth) ^ 10 := by
        gcongr
      _ = (twoBlockCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10 := by
        rw [mul_pow]
        ring

/-- The common overhead exponent is strictly below one and dominates the
quadratic scheduler, incidence, and resource-slot exponents. -/
theorem twoBlock_overheadVolume_exponential_le
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator)) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
    let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
    let inputWidth := blockWidth + blockWidth
    let marginDenominator := twoBlockMarginDenominator denominator
    OverheadBound.overheadVolume copies 1 width schedulerDepth routingDepth <=
      twoBlockVolumeConstant denominator *
        2 ^ ((marginDenominator - 1) * inputWidth / marginDenominator) := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
  let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
  let inputWidth := blockWidth + blockWidth
  let marginDenominator := twoBlockMarginDenominator denominator
  let requestExponent := numerator * inputWidth / denominator
  let fieldExponent := inputWidth / marginDenominator
  let commonExponent := (marginDenominator - 1) * inputWidth /
    marginDenominator
  let fieldConstant := twoBlockFieldConstant denominator
  let slotConstant := twoBlockSlotConstant denominator
  have marginPositive : 0 < marginDenominator := by
    dsimp [marginDenominator]
    unfold twoBlockMarginDenominator
    omega
  have dimensionPositive' : 0 < dimension := dimensionPositive
  have marginEq : marginDenominator = 6 * denominator := by
    dsimp [marginDenominator]
    rfl
  have dimensionEq : dimension = 3 * denominator := by
    dsimp [dimension]
    rfl
  have requestRescale : requestExponent =
      6 * numerator * inputWidth / marginDenominator := by
    dsimp [requestExponent]
    rw [marginEq]
    have rescaled := Nat.mul_div_mul_left (m := 6)
      (numerator * inputWidth) denominator (by omega)
    rw [show 6 * numerator * inputWidth =
      6 * (numerator * inputWidth) by ring]
    exact rescaled.symm
  have fieldRescale : blockWidth / dimension = fieldExponent := by
    dsimp [fieldExponent, inputWidth]
    rw [marginEq, dimensionEq]
    have rescaled := Nat.mul_div_mul_left (m := 2) blockWidth
      (3 * denominator) (by omega)
    have denominatorSum : 6 * denominator =
        3 * denominator + 3 * denominator := by omega
    rw [denominatorSum]
    simpa only [two_mul] using rescaled.symm
  have fieldBound : 2 ^ width <=
      fieldConstant * 2 ^ fieldExponent := by
    have selected := fieldCard_le blockWidth dimension dimensionPositive
    dsimp [fieldConstant]
    rw [fieldRescale] at selected
    exact selected
  have slotBound : 2 ^ (dimension * width) <=
      slotConstant * 2 ^ blockWidth := by
    have selected := fieldCard_pow_dimension_le blockWidth dimension
      dimensionPositive
    exact selected
  have schedulerExponentBound :
      requestExponent + requestExponent + fieldExponent <= commonExponent := by
    have twiceFloored : 2 * requestExponent <=
        (12 * numerator * inputWidth) / marginDenominator := by
      rw [requestRescale]
      calc
        2 * (6 * numerator * inputWidth / marginDenominator) <=
            2 * (6 * numerator * inputWidth) / marginDenominator :=
          Nat.mul_div_le_mul_div_assoc 2
            (6 * numerator * inputWidth) marginDenominator
        _ = (12 * numerator * inputWidth) / marginDenominator := by
          apply congrArg (fun value => value / marginDenominator)
          ring
    have combined :
        (12 * numerator * inputWidth) / marginDenominator +
            inputWidth / marginDenominator <=
          ((12 * numerator + 1) * inputWidth) / marginDenominator := by
      calc
        (12 * numerator * inputWidth) / marginDenominator +
            inputWidth / marginDenominator <=
          (12 * numerator * inputWidth + inputWidth) /
            marginDenominator :=
          Growth.div_add_div_le _ _ _ marginPositive
        _ = ((12 * numerator + 1) * inputWidth) /
            marginDenominator := by
          apply congrArg (fun value => value / marginDenominator)
          ring
    have coefficientBound : 12 * numerator + 1 <= marginDenominator - 1 := by
      rw [marginEq]
      omega
    calc
      requestExponent + requestExponent + fieldExponent =
          2 * requestExponent + fieldExponent := by omega
      _ <= (12 * numerator * inputWidth) / marginDenominator +
          fieldExponent := Nat.add_le_add_right twiceFloored _
      _ <= ((12 * numerator + 1) * inputWidth) /
          marginDenominator := by
        dsimp [fieldExponent]
        exact combined
      _ <= commonExponent := by
        dsimp [commonExponent]
        exact Nat.div_le_div_right
          (Nat.mul_le_mul_right inputWidth coefficientBound)
  have incidenceExponentBound :
      requestExponent + fieldExponent <= commonExponent := by
    calc
      requestExponent + fieldExponent =
          0 + (requestExponent + fieldExponent) := by omega
      _ <= requestExponent + (requestExponent + fieldExponent) :=
        Nat.add_le_add_right (Nat.zero_le requestExponent) _
      _ = requestExponent + requestExponent + fieldExponent := by omega
      _ <= commonExponent := schedulerExponentBound
  have slotExponentBound : blockWidth <= commonExponent := by
    apply (Nat.le_div_iff_mul_le marginPositive).2
    dsimp [commonExponent, inputWidth]
    rw [marginEq]
    have marginAtLeastTwo : 2 <= 6 * denominator := by omega
    calc
      blockWidth * (6 * denominator) <=
          blockWidth * (2 * (6 * denominator - 1)) := by
        exact Nat.mul_le_mul_left blockWidth (by omega)
      _ = (6 * denominator - 1) *
          (blockWidth + blockWidth) := by ring
  have schedulerPowerBound :
      copies * copies * 2 ^ width <=
        fieldConstant * 2 ^ commonExponent := by
    calc
      copies * copies * 2 ^ width <=
          2 ^ requestExponent * 2 ^ requestExponent *
            (fieldConstant * 2 ^ fieldExponent) := by gcongr
      _ = fieldConstant *
          2 ^ (requestExponent + requestExponent + fieldExponent) := by
        rw [Nat.pow_add, Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExponent :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) schedulerExponentBound)
  have incidencePowerBound : copies * 2 ^ width <=
      fieldConstant * 2 ^ commonExponent := by
    calc
      copies * 2 ^ width <=
          2 ^ requestExponent * (fieldConstant * 2 ^ fieldExponent) := by
        gcongr
      _ = fieldConstant * 2 ^ (requestExponent + fieldExponent) := by
        rw [Nat.pow_add]
        ring
      _ <= fieldConstant * 2 ^ commonExponent :=
        Nat.mul_le_mul_left fieldConstant
          (Nat.pow_le_pow_right (by omega) incidenceExponentBound)
  have slotPowerBound : 2 ^ (dimension * width) <=
      slotConstant * 2 ^ commonExponent := by
    exact slotBound.trans <| Nat.mul_le_mul_left slotConstant
      (Nat.pow_le_pow_right (by omega) slotExponentBound)
  have schedulerScaled : 2 * copies * copies * 2 ^ width <=
      2 * (fieldConstant * 2 ^ commonExponent) := by
    calc
      2 * copies * copies * 2 ^ width =
          2 * (copies * copies * 2 ^ width) := by ring
      _ <= 2 * (fieldConstant * 2 ^ commonExponent) :=
        Nat.mul_le_mul_left 2 schedulerPowerBound
  have incidenceScaled : 7 * copies * 2 ^ width <=
      7 * (fieldConstant * 2 ^ commonExponent) := by
    calc
      7 * copies * 2 ^ width = 7 * (copies * 2 ^ width) := by ring
      _ <= 7 * (fieldConstant * 2 ^ commonExponent) :=
        Nat.mul_le_mul_left 7 incidencePowerBound
  have slotsScaled : 4 * 2 ^ (dimension * width) <=
      4 * (slotConstant * 2 ^ commonExponent) :=
    Nat.mul_le_mul_left 4 slotPowerBound
  calc
    OverheadBound.overheadVolume copies 1 width schedulerDepth routingDepth <=
        2 * copies * copies * 2 ^ width +
          7 * copies * 2 ^ width +
          4 * 2 ^ (dimension * width) :=
      twoBlock_overheadVolume_le denominator blockWidth copies
        denominatorPositive copiesPositive
    _ <= 2 * (fieldConstant * 2 ^ commonExponent) +
        7 * (fieldConstant * 2 ^ commonExponent) +
        4 * (slotConstant * 2 ^ commonExponent) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          schedulerScaled incidenceScaled)
        slotsScaled
    _ = twoBlockVolumeConstant denominator * 2 ^ commonExponent := by
      unfold twoBlockVolumeConstant
      dsimp [fieldConstant, slotConstant]
      ring

end EqualBlock
end MassProduction
end Algebraic
