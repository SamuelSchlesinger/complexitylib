/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BlockInductionVolumeBound

/-!
# Polynomial overhead absorption for block induction

This module combines the finite ledger with the strict live-volume exponent
and proves that every non-resource cost in one equal-block induction step is
eventually bounded by one Shannon-scale unit.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace BlockInduction

open CodeParameters

/-! ## Absorbing the polynomial ledger -/

/-- Slope relating ledger widths to the complete input width. -/
def stepParameterSlope (denominator : Nat) : Nat :=
  let dimension := stepDimension denominator
  3 + (dimension + 1) * (4 * dimension + 4)

/-- Constant coefficient of the degree-ten polynomial ledger envelope. -/
def stepCoefficientConstant (denominator : Nat) : Nat :=
  let slope := stepParameterSlope denominator
  1000000 * (slope + 1) ^ 10 + 5 * slope

theorem step_parameterBound_le
    (level denominator blockWidth : Nat) :
    stepParameterBound level denominator blockWidth <=
      stepParameterSlope denominator *
        (stepInputWidth level blockWidth + 1) := by
  let dimension := stepDimension denominator
  let inputWidth := stepInputWidth level blockWidth
  let widthBound := stepWidthBound level denominator blockWidth
  let slope := stepParameterSlope denominator
  have widthLinear : widthBound <=
      (4 * dimension + 4) * (inputWidth + 1) := by
    dsimp [widthBound, stepWidthBound]
    change inputWidth + 4 * dimension + 3 <= _
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

theorem step_coefficient_le
    (level denominator blockWidth : Nat) :
    let parameterBound := stepParameterBound level denominator blockWidth
    let inputWidth := stepInputWidth level blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      stepCoefficientConstant denominator * (inputWidth + 1) ^ 10 := by
  dsimp only
  let parameterBound := stepParameterBound level denominator blockWidth
  let inputWidth := stepInputWidth level blockWidth
  let slope := stepParameterSlope denominator
  have parameterLinear : parameterBound <= slope * (inputWidth + 1) :=
    step_parameterBound_le level denominator blockWidth
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
    _ = stepCoefficientConstant denominator *
        (inputWidth + 1) ^ 10 := by
      unfold stepCoefficientConstant
      dsimp [slope]
      ring

theorem step_coefficient_le_monomial
    (level denominator blockWidth : Nat)
    (blockPositive : 0 < blockWidth) :
    let parameterBound := stepParameterBound level denominator blockWidth
    let inputWidth := stepInputWidth level blockWidth
    OverheadBound.coefficientEnvelope parameterBound + 5 * parameterBound <=
      (stepCoefficientConstant denominator * 2 ^ 10) *
        inputWidth ^ 10 := by
  dsimp only
  let inputWidth := stepInputWidth level blockWidth
  have inputPositive : 0 < inputWidth := by
    dsimp [inputWidth, stepInputWidth]
    positivity
  have successorBound : inputWidth + 1 <= 2 * inputWidth := by omega
  exact (step_coefficient_le level denominator blockWidth).trans <| by
    calc
      stepCoefficientConstant denominator * (inputWidth + 1) ^ 10 <=
          stepCoefficientConstant denominator * (2 * inputWidth) ^ 10 := by
        gcongr
      _ = (stepCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10 := by
        rw [mul_pow]
        ring

/-- Fixed coefficient of the polynomial-times-exponential overhead bound. -/
def stepOverheadConstant (denominator : Nat) : Nat :=
  stepVolumeConstant denominator *
    (stepCoefficientConstant denominator * 2 ^ 10)

/-- Pointwise composition of the exact ledger, the live-volume estimate, and
the common polynomial coefficient estimate. -/
theorem step_overhead_le_of_growth
    (level numerator denominator blockWidth copies : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator)
    (blockLarge : 4 * denominator <= blockWidth)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * stepInputWidth level blockWidth / denominator))
    (growthBound :
      stepOverheadConstant denominator *
          stepInputWidth level blockWidth ^ 10 *
          2 ^ stepCommonExponent level denominator blockWidth <=
        2 ^ stepInputWidth level blockWidth /
          stepInputWidth level blockWidth) :
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
    CompositionBound.overheadCostBound copies groups blockWidth dimension width
        (stepSuffixWidth level blockWidth) schedulerDepth groupBitWidth
        orderWidth routingDepth routingDepth <=
      2 ^ stepInputWidth level blockWidth /
        stepInputWidth level blockWidth := by
  dsimp only
  let dimension := stepDimension denominator
  let dimensionPositive := stepDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let groups := groupCount level denominator blockWidth
  let suffixWidth := stepSuffixWidth level blockWidth
  let schedulerDepth := FiniteParameters.schedulerDepth copies groups width
  let groupBitWidth := FiniteParameters.groupBitWidth groups
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth :=
    FiniteParameters.routingDepth copies groups dimension width
  let parameterBound := stepParameterBound level denominator blockWidth
  let inputWidth := stepInputWidth level blockWidth
  let commonExponent := stepCommonExponent level denominator blockWidth
  obtain ⟨dimensionBound, widthBound, schedulerBound, prefixBound,
      keyBound, suffixBound, orderBound, routingBound⟩ :=
    step_parameters_bounded level numerator denominator blockWidth copies
      levelAtLeastTwo denominatorPositive rateBelowLevel copiesBound
  have factored := OverheadBound.overheadCostBound_le_factored
    copies groups blockWidth dimension width suffixWidth schedulerDepth
    groupBitWidth orderWidth routingDepth
    (fieldWidth_positive blockWidth dimension dimensionPositive)
  have byVolume := OverheadBound.factoredOverhead_le_volume_mul_envelope
    copies groups blockWidth dimension width suffixWidth schedulerDepth
    groupBitWidth orderWidth routingDepth parameterBound dimensionBound
    widthBound schedulerBound prefixBound keyBound suffixBound orderBound
    routingBound
  have volumeBound := step_overheadVolume_exponential_le level numerator
    denominator blockWidth copies levelAtLeastTwo denominatorPositive
    rateBelowLevel blockLarge copiesPositive copiesBound
  have coefficientBound := step_coefficient_le_monomial level denominator
    blockWidth (by omega)
  calc
    CompositionBound.overheadCostBound copies groups blockWidth dimension width
        suffixWidth schedulerDepth groupBitWidth orderWidth routingDepth
        routingDepth <=
      OverheadBound.factoredOverhead copies groups blockWidth dimension width
        suffixWidth schedulerDepth groupBitWidth orderWidth routingDepth :=
      factored
    _ <= OverheadBound.overheadVolume copies groups width schedulerDepth
          routingDepth *
        (OverheadBound.coefficientEnvelope parameterBound +
          5 * parameterBound) := byVolume
    _ <= (stepVolumeConstant denominator * 2 ^ commonExponent) *
        ((stepCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10) := Nat.mul_le_mul volumeBound coefficientBound
    _ = stepOverheadConstant denominator * inputWidth ^ 10 *
        2 ^ commonExponent := by
      unfold stepOverheadConstant
      ring
    _ <= 2 ^ inputWidth / inputWidth := growthBound

/-- All non-resource work is eventually at most one Shannon-scale unit,
uniformly over every permitted batch. -/
theorem eventually_step_overhead_le
    (level numerator denominator : Nat)
    (levelAtLeastTwo : 2 <= level)
    (denominatorPositive : 0 < denominator)
    (rateBelowLevel : (level + 1) * numerator < level * denominator) :
    ∀ᶠ blockWidth in Filter.atTop,
      ∀ copies : Nat,
        0 < copies ->
        copies <=
          2 ^ (numerator * stepInputWidth level blockWidth / denominator) ->
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
        CompositionBound.overheadCostBound copies groups blockWidth dimension
            width (stepSuffixWidth level blockWidth) schedulerDepth
            groupBitWidth orderWidth routingDepth routingDepth <=
          2 ^ stepInputWidth level blockWidth /
            stepInputWidth level blockWidth := by
  let marginDenominator := stepMarginDenominator level denominator
  have marginPositive : 0 < marginDenominator :=
    stepMarginDenominator_positive level denominator denominatorPositive
  have marginProper : marginDenominator - 1 < marginDenominator := by omega
  have growth := Growth.eventually_mul_two_pow_rational_le_shannonScale
    (stepOverheadConstant denominator) 10 (marginDenominator - 1)
    marginDenominator marginPositive marginProper
  obtain ⟨cutoff, pastCutoff⟩ := Filter.eventually_atTop.1 growth
  apply Filter.eventually_atTop.2
  refine ⟨max cutoff (max 1 (4 * denominator)),
    fun blockWidth blockLarge copies copiesPositive copiesBound => ?_⟩
  have blockPositive : 0 < blockWidth := by omega
  have inputPastCutoff : cutoff <= stepInputWidth level blockWidth := by
    have blockPast : cutoff <= blockWidth := by omega
    unfold stepInputWidth
    omega
  have growthBound := pastCutoff (stepInputWidth level blockWidth)
    inputPastCutoff
  exact step_overhead_le_of_growth level numerator denominator blockWidth
    copies levelAtLeastTwo denominatorPositive rateBelowLevel (by omega)
    copiesPositive copiesBound
    (by simpa [stepCommonExponent, marginDenominator] using growthBound)

end BlockInduction
end MassProduction
end Algebraic
