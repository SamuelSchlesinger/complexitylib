/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BlockParameters

/-!
# Denominator-free leading-coefficient accounting

Multiply the code-storage and shorter-function precision inequalities,
transfer the suffix normalization to the original input length, and add the
reserved runtime-overhead allowance. All arithmetic takes place in the
natural numbers; no floor approximation or division loss is introduced.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.CoefficientParameters

variable (parameters : CoefficientParameters numerator denominator precision)

/-- Exact integer rate, synthesis, split, and overhead bounds imply the
target normalized coefficient for the complete finite circuit cost. -/
theorem cost_le_coefficient
    (inputSplit : prefixWidth + suffixWidth = inputs)
    (suffixFraction : parameters.geometry.suffixSlope * inputs ≤ parameters.geometry.inputSlope * suffixWidth)
    (storage : parameters.resourcePrecision * resources ≤ (parameters.resourcePrecision + 2) * 2 ^ prefixWidth)
    (synthesis : parameters.resourcePrecision * resourceCost * suffixWidth ≤
      (parameters.resourcePrecision + 1) * 2 ^ suffixWidth)
    (runtime : 2 * precision * (denominator - numerator) * inputs * overhead ≤ denominator * 2 ^ inputs) :
    precision * (denominator - numerator) * inputs * (overhead + resources * resourceCost) ≤
      (precision + 1) * denominator * 2 ^ inputs := by
  let scale := parameters.geometry.suffixSlope * parameters.resourcePrecision ^ 2
  have scalePositive : 0 < scale := Nat.mul_pos parameters.geometry.suffixSlope_positive (by
    exact pow_pos parameters.resourcePositive _)
  have product : parameters.resourcePrecision ^ 2 * resources * resourceCost * suffixWidth ≤
      (parameters.resourcePrecision + 2) * (parameters.resourcePrecision + 1) * 2 ^ inputs := by
    calc
      _ = (parameters.resourcePrecision * resources) * (parameters.resourcePrecision * resourceCost * suffixWidth) := by ring
      _ ≤ ((parameters.resourcePrecision + 2) * 2 ^ prefixWidth) *
          ((parameters.resourcePrecision + 1) * 2 ^ suffixWidth) := Nat.mul_le_mul storage synthesis
      _ = (parameters.resourcePrecision + 2) * (parameters.resourcePrecision + 1) * 2 ^ (prefixWidth + suffixWidth) := by
        rw [pow_add]; ring
      _ = _ := by rw [inputSplit]
  have leadingScaled :
      (2 * precision * (denominator - numerator) * inputs * (resources * resourceCost)) * scale ≤
        ((2 * precision + 1) * denominator * 2 ^ inputs) * scale := by
    calc
      _ = (2 * precision * (denominator - numerator)) * (parameters.geometry.suffixSlope * inputs) *
          (parameters.resourcePrecision ^ 2 * resources * resourceCost) := by dsimp [scale]; ring
      _ ≤ (2 * precision * (denominator - numerator)) * (parameters.geometry.inputSlope * suffixWidth) *
          (parameters.resourcePrecision ^ 2 * resources * resourceCost) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ suffixFraction)
      _ = (2 * precision * (denominator - numerator) * parameters.geometry.inputSlope) *
          (parameters.resourcePrecision ^ 2 * resources * resourceCost * suffixWidth) := by ring
      _ ≤ (2 * precision * (denominator - numerator) * parameters.geometry.inputSlope) *
          ((parameters.resourcePrecision + 2) * (parameters.resourcePrecision + 1) * 2 ^ inputs) :=
        Nat.mul_le_mul_left _ product
      _ = (2 * precision * (denominator - numerator) * parameters.geometry.inputSlope *
          (parameters.resourcePrecision + 2) * (parameters.resourcePrecision + 1)) * 2 ^ inputs := by ring
      _ ≤ ((2 * precision + 1) * denominator * parameters.geometry.suffixSlope *
          parameters.resourcePrecision ^ 2) * 2 ^ inputs :=
        Nat.mul_le_mul_right _ parameters.leadingCoefficient
      _ = _ := by dsimp [scale]; ring
  have leading : 2 * precision * (denominator - numerator) * inputs * (resources * resourceCost) ≤
      (2 * precision + 1) * denominator * 2 ^ inputs := by nlinarith
  have combined := Nat.add_le_add runtime leading
  nlinarith

end Algebraic.MassProduction.Nonuniform.CoefficientParameters
