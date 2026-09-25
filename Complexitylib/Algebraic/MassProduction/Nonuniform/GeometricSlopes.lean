/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CodeQuantitative

/-!
# Integer slopes inside a prescribed rational interval

Choose a fixed field block width and dimension, then reserve a strict gap
between the allowed copy exponent and projective-direction capacity. The
prefix fraction can still lie in any prescribed interval above that copy
exponent. This is an exact integer construction, without limiting notation.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

/-- Numerical slopes supporting a geometric scheduler and a prescribed
upper bound on the fraction of input bits used as source prefixes. -/
structure GeometricSlopes (numerator denominator upperNumerator upperDenominator : Nat) where
  /-- Affine-space dimension, fixed independently of the input length. -/
  dimension : Nat
  /-- Bits per field block on the selected field-size subsequence. -/
  blockWidth : Nat
  /-- Scheduled batch exponent per complete field block. -/
  copySlope : Nat
  /-- Input bits per complete field block. -/
  inputSlope : Nat
  /-- Every field block has positive width. -/
  blockPositive : 0 < blockWidth
  /-- The affine space has positive dimension. -/
  dimensionPositive : 0 < dimension
  /-- The common-zero-block code admits the selected dimension. -/
  dimensionFits : dimension ≤ 2 ^ blockWidth
  /-- Strict exponential room absorbs the scheduler's fixed packing constant. -/
  directionSlack : copySlope + blockWidth + 1 ≤ blockWidth * (dimension - 1)
  /-- The prefix leaves a positive suffix slope. -/
  splitPositive : dimension * blockWidth + 1 < inputSlope
  /-- The scheduled exponent strictly exceeds the requested exponent. -/
  copyRate : numerator * inputSlope < denominator * copySlope
  /-- The prefix fraction is below the chosen coefficient threshold. -/
  prefixRate : upperDenominator * (dimension * blockWidth + 1) < upperNumerator * inputSlope

/-- Every nonempty rational interval above the copy exponent contains the
prefix fraction of a suitable geometric parameter choice. -/
theorem existsGeometricSlopes
    (proper : numerator < denominator) (upperPositive : 0 < upperNumerator)
    (upperProper : upperNumerator < upperDenominator)
    (between : numerator * upperDenominator < denominator * upperNumerator) :
    Nonempty (GeometricSlopes numerator denominator upperNumerator upperDenominator) := by
  let centerNumerator := numerator + upperNumerator
  let centerDenominator := denominator + upperDenominator
  have centerPositive : 0 < centerNumerator := by dsimp [centerNumerator]; omega
  have centerProper : centerNumerator < centerDenominator := by dsimp [centerNumerator, centerDenominator]; omega
  have centerLower : numerator * centerDenominator < denominator * centerNumerator := by
    dsimp [centerNumerator, centerDenominator]
    nlinarith
  have centerUpper : upperDenominator * centerNumerator < upperNumerator * centerDenominator := by
    dsimp [centerNumerator, centerDenominator]
    nlinarith
  let size := 10 * (denominator + numerator + 1) * (centerNumerator + 1) + 3
  let prefixSlope := size * size + 1
  let copySlope := size * (size - 3)
  let inputSlope := centerDenominator * prefixSlope / centerNumerator + 1
  have sizeLarge : 3 ≤ size := by dsimp [size]; omega
  have sizePositive : 0 < size := by omega
  have squareGap : centerNumerator * denominator * (3 * size + 1) + centerNumerator * numerator < prefixSlope := by
    have first : 3 * centerNumerator * denominator + 1 ≤ size := by dsimp [size]; nlinarith
    have second : centerNumerator * denominator + centerNumerator * numerator < size := by dsimp [size]; nlinarith
    dsimp [prefixSlope]
    nlinarith
  have prefixIdentity : prefixSlope = copySlope + 3 * size + 1 := by
    have subtraction := Nat.sub_add_cancel sizeLarge
    dsimp [prefixSlope, copySlope]
    nlinarith
  have inputLower : centerDenominator * prefixSlope < inputSlope * centerNumerator := by
    dsimp [inputSlope]
    have remainder := Nat.mod_lt (centerDenominator * prefixSlope) centerPositive
    have division := Nat.mod_add_div (centerDenominator * prefixSlope) centerNumerator
    nlinarith
  have inputUpper : inputSlope * centerNumerator ≤ centerDenominator * prefixSlope + centerNumerator := by
    dsimp [inputSlope]
    have division := Nat.div_mul_le_self (centerDenominator * prefixSlope) centerNumerator
    nlinarith
  have splitPositive : prefixSlope < inputSlope := by
    have prefixLe : prefixSlope ≤ centerDenominator * prefixSlope / centerNumerator := by
      apply (Nat.le_div_iff_mul_le centerPositive).mpr
      nlinarith
    dsimp [inputSlope]
    omega
  have copyRate : numerator * inputSlope < denominator * copySlope := by
    apply (Nat.mul_lt_mul_right centerPositive).mp
    have gapScaled := Nat.mul_le_mul_right prefixSlope (Nat.succ_le_of_lt centerLower)
    have upperScaled := Nat.mul_le_mul_left numerator inputUpper
    have prefixScaled : denominator * centerNumerator * prefixSlope =
        denominator * centerNumerator * copySlope + centerNumerator * denominator * (3 * size + 1) := by
      rw [prefixIdentity]
      ring
    nlinarith
  have prefixRate : upperDenominator * prefixSlope < upperNumerator * inputSlope := by
    apply (Nat.mul_lt_mul_right centerPositive).mp
    have inputScaled := Nat.mul_lt_mul_of_pos_left inputLower upperPositive
    have centerScaled := Nat.mul_le_mul_right prefixSlope centerUpper.le
    nlinarith
  refine ⟨{
    dimension := size
    blockWidth := size
    copySlope := copySlope
    inputSlope := inputSlope
    blockPositive := sizePositive
    dimensionPositive := sizePositive
    dimensionFits := (Nat.lt_pow_self (by omega : 1 < 2)).le
    directionSlack := ?_
    splitPositive := splitPositive
    copyRate := copyRate
    prefixRate := prefixRate
  }⟩
  have first := Nat.sub_add_cancel sizeLarge
  have second := Nat.sub_add_cancel (by omega : 1 ≤ size)
  dsimp [copySlope]
  nlinarith

end Algebraic.MassProduction.Nonuniform
