/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.EqualBlockVolumeBound
public import Complexitylib.Algebraic.MassProduction.Growth
public import Complexitylib.Algebraic.MassProduction.OverheadBound

/-!
# Polynomial overhead absorption for the two-block base case

This module combines the two-block finite ledger with its strict exponential
volume bound and proves that the complete non-resource overhead is eventually
at most one Shannon-scale unit.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters

/-- Fixed coefficient multiplying the polynomial-times-subunit-exponential
upper bound for every non-resource gate. -/
def twoBlockOverheadConstant (denominator : Nat) : Nat :=
  twoBlockVolumeConstant denominator *
    (twoBlockCoefficientConstant denominator * 2 ^ 10)

/-- Pointwise composition of the exact ledger, record-volume estimate, and
polynomial coefficient estimate. -/
theorem twoBlock_overhead_le_of_growth
    (numerator denominator blockWidth copies : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator)
    (blockPositive : 0 < blockWidth)
    (copiesPositive : 0 < copies)
    (copiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator))
    (growthBound :
      twoBlockOverheadConstant denominator *
          (blockWidth + blockWidth) ^ 10 *
          2 ^ ((twoBlockMarginDenominator denominator - 1) *
            (blockWidth + blockWidth) /
              twoBlockMarginDenominator denominator) <=
        2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth)) :
    let dimension := twoBlockDimension denominator
    let dimensionPositive := twoBlockDimension_positive denominatorPositive
    let width := fieldWidth blockWidth dimension dimensionPositive
    let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
    let groupBitWidth := FiniteParameters.groupBitWidth 1
    let orderWidth := FiniteParameters.orderWidth copies width
    let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
    CompositionBound.overheadCostBound copies 1 blockWidth dimension width
        blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
        routingDepth <=
      2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth) := by
  dsimp only
  let dimension := twoBlockDimension denominator
  let dimensionPositive := twoBlockDimension_positive denominatorPositive
  let width := fieldWidth blockWidth dimension dimensionPositive
  let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
  let groupBitWidth := FiniteParameters.groupBitWidth 1
  let orderWidth := FiniteParameters.orderWidth copies width
  let routingDepth := FiniteParameters.routingDepth copies 1 dimension width
  let parameterBound := twoBlockParameterBound denominator blockWidth
  let inputWidth := blockWidth + blockWidth
  let commonExponent := (twoBlockMarginDenominator denominator - 1) *
    inputWidth / twoBlockMarginDenominator denominator
  obtain ⟨dimensionBound, widthBound, schedulerBound, prefixBound,
      keyBound, suffixBound, orderBound, routingBound⟩ :=
    twoBlock_parameters_bounded numerator denominator blockWidth copies
      denominatorPositive rateBelowHalf copiesBound
  have factored := OverheadBound.overheadCostBound_le_factored
    copies 1 blockWidth dimension width blockWidth schedulerDepth
    groupBitWidth orderWidth routingDepth
    (fieldWidth_positive blockWidth dimension dimensionPositive)
  have byVolume := OverheadBound.factoredOverhead_le_volume_mul_envelope
    copies 1 blockWidth dimension width blockWidth schedulerDepth
    groupBitWidth orderWidth routingDepth parameterBound dimensionBound
    widthBound schedulerBound prefixBound keyBound suffixBound orderBound
    routingBound
  have volumeBound := twoBlock_overheadVolume_exponential_le
    numerator denominator blockWidth copies denominatorPositive rateBelowHalf
    copiesPositive copiesBound
  have coefficientBound := twoBlock_coefficient_le_monomial
    denominator blockWidth blockPositive
  calc
    CompositionBound.overheadCostBound copies 1 blockWidth dimension width
        blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
        routingDepth <=
      OverheadBound.factoredOverhead copies 1 blockWidth dimension width
        blockWidth schedulerDepth groupBitWidth orderWidth routingDepth :=
      factored
    _ <= OverheadBound.overheadVolume copies 1 width schedulerDepth
          routingDepth *
        (OverheadBound.coefficientEnvelope parameterBound +
          5 * parameterBound) := byVolume
    _ <= (twoBlockVolumeConstant denominator * 2 ^ commonExponent) *
        ((twoBlockCoefficientConstant denominator * 2 ^ 10) *
          inputWidth ^ 10) := Nat.mul_le_mul volumeBound coefficientBound
    _ = twoBlockOverheadConstant denominator * inputWidth ^ 10 *
        2 ^ commonExponent := by
      unfold twoBlockOverheadConstant
      ring
    _ <= 2 ^ inputWidth / inputWidth := growthBound

/-- The polynomial ledger is eventually absorbed by its strict binary
exponent margin, uniformly over every permitted batch at the fixed rate. -/
theorem eventually_twoBlock_overhead_le
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator) :
    ∀ᶠ blockWidth in Filter.atTop,
      ∀ copies : Nat,
        0 < copies ->
        copies <=
          2 ^ (numerator * (blockWidth + blockWidth) / denominator) ->
        let dimension := twoBlockDimension denominator
        let dimensionPositive :=
          twoBlockDimension_positive denominatorPositive
        let width := fieldWidth blockWidth dimension dimensionPositive
        let schedulerDepth := FiniteParameters.schedulerDepth copies 1 width
        let groupBitWidth := FiniteParameters.groupBitWidth 1
        let orderWidth := FiniteParameters.orderWidth copies width
        let routingDepth :=
          FiniteParameters.routingDepth copies 1 dimension width
        CompositionBound.overheadCostBound copies 1 blockWidth dimension width
            blockWidth schedulerDepth groupBitWidth orderWidth routingDepth
            routingDepth <=
          2 ^ (blockWidth + blockWidth) / (blockWidth + blockWidth) := by
  let marginDenominator := twoBlockMarginDenominator denominator
  have marginPositive : 0 < marginDenominator := by
    dsimp [marginDenominator]
    unfold twoBlockMarginDenominator
    omega
  have marginProper : marginDenominator - 1 < marginDenominator := by omega
  have growth := Growth.eventually_mul_two_pow_rational_le_shannonScale
    (twoBlockOverheadConstant denominator) 10 (marginDenominator - 1)
    marginDenominator marginPositive marginProper
  obtain ⟨cutoff, pastCutoff⟩ := Filter.eventually_atTop.1 growth
  apply Filter.eventually_atTop.2
  refine ⟨max cutoff 1, fun blockWidth blockLarge copies copiesPositive
    copiesBound => ?_⟩
  have inputPastCutoff : cutoff <= blockWidth + blockWidth := by omega
  have growthBound := pastCutoff (blockWidth + blockWidth) inputPastCutoff
  exact twoBlock_overhead_le_of_growth numerator denominator blockWidth copies
    denominatorPositive rateBelowHalf (by omega) copiesPositive copiesBound
    (by simpa only [marginDenominator] using growthBound)

end EqualBlock
end MassProduction
end Algebraic
