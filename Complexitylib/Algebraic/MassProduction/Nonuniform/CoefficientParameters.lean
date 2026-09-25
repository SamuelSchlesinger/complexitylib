/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricSlopes

/-!
# Parameters approaching the coefficient `1 / (1 - gamma)`

Choose a resource precision and a rational prefix fraction that leave half
of the requested coefficient error for runtime overhead. Integer geometric
slopes realize that fraction while retaining a strict direction-capacity
and copy-exponent gap.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

/-- Fixed numerical parameters with enough coefficient slack for the final
polynomial-overhead absorption. -/
structure CoefficientParameters (numerator denominator precision : Nat) where
  /-- Precision used for both the code rate and shorter-function synthesis. -/
  resourcePrecision : Nat
  /-- Auxiliary rational upper bound on the prefix fraction. -/
  upperNumerator : Nat
  /-- Denominator of that auxiliary rational upper bound. -/
  upperDenominator : Nat
  /-- Integer field, copy, and input slopes inside the allowed interval. -/
  geometry : GeometricSlopes numerator denominator upperNumerator upperDenominator
  /-- The resource precision is positive. -/
  resourcePositive : 0 < resourcePrecision
  /-- The leading resource cost uses at most half of the target error allowance. -/
  leadingCoefficient :
    2 * precision * (denominator - numerator) * geometry.inputSlope *
        (resourcePrecision + 2) * (resourcePrecision + 1) ≤
      (2 * precision + 1) * denominator *
        (geometry.inputSlope - (geometry.dimension * geometry.blockWidth + 1)) * resourcePrecision ^ 2

/-- Every rational copy exponent below one and every positive target
precision admit fixed parameters with the required leading-coefficient slack. -/
theorem existsCoefficientParameters (proper : numerator < denominator) (precisionPositive : 0 < precision) :
    Nonempty (CoefficientParameters numerator denominator precision) := by
  let resourcePrecision := 12 * precision + 10
  let upperDenominator := (2 * precision + 1) * denominator * resourcePrecision ^ 2
  let loss := 2 * precision * (denominator - numerator) * (resourcePrecision + 2) * (resourcePrecision + 1)
  let upperNumerator := upperDenominator - loss
  have denominatorPositive : 0 < denominator := by omega
  have gapPositive : 0 < denominator - numerator := Nat.sub_pos_iff_lt.mpr proper
  have resourcePositive : 0 < resourcePrecision := by dsimp [resourcePrecision]; omega
  have sharpMargin : 2 * precision * (resourcePrecision + 2) * (resourcePrecision + 1) <
      (2 * precision + 1) * resourcePrecision ^ 2 := by
    dsimp [resourcePrecision]
    nlinarith
  have lossPositive : 0 < loss := by dsimp [loss]; positivity
  have lossSmall : loss < upperDenominator := by
    calc
      _ = (denominator - numerator) * (2 * precision * (resourcePrecision + 2) * (resourcePrecision + 1)) := by
        dsimp [loss]; ring
      _ ≤ denominator * (2 * precision * (resourcePrecision + 2) * (resourcePrecision + 1)) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ < denominator * ((2 * precision + 1) * resourcePrecision ^ 2) :=
        Nat.mul_lt_mul_of_pos_left sharpMargin denominatorPositive
      _ = _ := by dsimp [upperDenominator]; ring
  have upperAdd : upperNumerator + loss = upperDenominator := Nat.sub_add_cancel lossSmall.le
  have upperPositive : 0 < upperNumerator := Nat.sub_pos_iff_lt.mpr lossSmall
  have upperProper : upperNumerator < upperDenominator := by omega
  have gapScaled : denominator * loss < (denominator - numerator) * upperDenominator := by
    calc
      _ = (denominator * (denominator - numerator)) *
          (2 * precision * (resourcePrecision + 2) * (resourcePrecision + 1)) := by dsimp [loss]; ring
      _ < (denominator * (denominator - numerator)) * ((2 * precision + 1) * resourcePrecision ^ 2) :=
        Nat.mul_lt_mul_of_pos_left sharpMargin (Nat.mul_pos denominatorPositive gapPositive)
      _ = _ := by dsimp [upperDenominator]; ring
  have between : numerator * upperDenominator < denominator * upperNumerator := by
    have gapIdentity : (denominator - numerator) * upperDenominator + numerator * upperDenominator =
        denominator * upperDenominator := by rw [← Nat.add_mul, Nat.sub_add_cancel proper.le]
    have upperIdentity : denominator * upperNumerator + denominator * loss = denominator * upperDenominator := by
      rw [← Nat.mul_add, upperAdd]
    nlinarith
  obtain ⟨geometry⟩ := existsGeometricSlopes proper upperPositive upperProper between
  refine ⟨⟨resourcePrecision, upperNumerator, upperDenominator, geometry, resourcePositive, ?_⟩⟩
  have prefixRate := geometry.prefixRate
  have split := Nat.sub_add_cancel geometry.splitPositive.le
  have upperScaled : upperNumerator * geometry.inputSlope + loss * geometry.inputSlope =
      upperDenominator * geometry.inputSlope := by rw [← Nat.add_mul, upperAdd]
  have splitScaled : upperDenominator *
      (geometry.inputSlope - (geometry.dimension * geometry.blockWidth + 1)) +
      upperDenominator * (geometry.dimension * geometry.blockWidth + 1) =
        upperDenominator * geometry.inputSlope := by rw [← Nat.mul_add, split]
  have leading : loss * geometry.inputSlope ≤ upperDenominator *
      (geometry.inputSlope - (geometry.dimension * geometry.blockWidth + 1)) := by nlinarith
  calc
    _ = loss * geometry.inputSlope := by dsimp [loss]; ring
    _ ≤ _ := leading
    _ = _ := by dsimp [upperDenominator]; ring

end Algebraic.MassProduction.Nonuniform
