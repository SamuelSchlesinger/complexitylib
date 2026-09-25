/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CoefficientParameters
public import Complexitylib.Algebraic.MassProduction.CodeParameters

/-!
# Parameters at every input length

Use `floor(inputs/inputSlope)` field blocks and put the remainder into the
suffix. The input length is exact, while the suffix fraction never falls
below its fixed rational slope. Fixed lower bounds on the block count
discharge the copy-exponent and direction-capacity margins.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GeometricSlopes

open Sorting
open scoped LinearAlgebra.Projectivization

variable (parameters : GeometricSlopes numerator denominator upperNumerator upperDenominator)

/-- Prefix bits per field block, with one extra block bit for rounding slack. -/
def prefixSlope : Nat := parameters.dimension * parameters.blockWidth + 1

/-- Complete field blocks at the current input length. -/
def blocks (inputs : Nat) : Nat := inputs / parameters.inputSlope

/-- Source-table prefix width. -/
def prefixWidth (inputs : Nat) : Nat := parameters.prefixSlope * parameters.blocks inputs

/-- Exact remaining input bits form the shorter function's suffix. -/
def suffixWidth (inputs : Nat) : Nat := inputs - parameters.prefixWidth inputs

/-- Binary-extension symbol width on the required block subsequence. -/
def fieldWidth (inputs : Nat) : Nat := parameters.blockWidth * parameters.blocks inputs

/-- Power-of-two scheduler batch depth. -/
def copyDepth (inputs : Nat) : Nat := parameters.copySlope * parameters.blocks inputs

/-- Positive slope of the shorter suffix. -/
def suffixSlope : Nat := parameters.inputSlope - parameters.prefixSlope

/-- The block divisor is positive. -/
theorem inputSlope_positive : 0 < parameters.inputSlope := by
  have := parameters.splitPositive
  omega

/-- At least one suffix bit is retained per full block. -/
theorem suffixSlope_positive : 0 < parameters.suffixSlope :=
  Nat.sub_pos_iff_lt.mpr parameters.splitPositive

/-- The source prefix fits at every input length. -/
theorem prefixWidth_le (inputs : Nat) : parameters.prefixWidth inputs ≤ inputs := by
  calc
    _ ≤ parameters.inputSlope * parameters.blocks inputs :=
      Nat.mul_le_mul_right _ parameters.splitPositive.le
    _ ≤ inputs := by
      simpa only [blocks, Nat.mul_comm] using Nat.div_mul_le_self inputs parameters.inputSlope

/-- Prefix and suffix exactly partition the original input length. -/
theorem prefix_add_suffix (inputs : Nat) : parameters.prefixWidth inputs + parameters.suffixWidth inputs = inputs :=
  Nat.add_sub_of_le (parameters.prefixWidth_le inputs)

/-- The slope gap bounds the incidence exponent by the prefix exponent. -/
theorem incidenceSlope_le : parameters.copySlope + parameters.blockWidth ≤ parameters.prefixSlope := by
  have slack := parameters.directionSlack
  have dimensionBound := Nat.mul_le_mul_left parameters.blockWidth (Nat.sub_le parameters.dimension 1)
  unfold prefixSlope
  nlinarith

/-- All generated request/scalar pairs fit in the source-table scale. -/
theorem pointBudget (inputs : Nat) : networkRecords (parameters.copyDepth inputs) * 2 ^ parameters.fieldWidth inputs ≤
    2 ^ parameters.prefixWidth inputs := by
  rw [networkRecords_eq_two_pow, ← pow_add]
  apply Nat.pow_le_pow_right (by omega)
  have scaled := Nat.mul_le_mul_right (parameters.blocks inputs) parameters.incidenceSlope_le
  simpa only [copyDepth, fieldWidth, prefixWidth, Nat.add_mul] using scaled

/-- The field bit width is no larger than the input length. -/
theorem fieldWidth_le (inputs : Nat) : parameters.fieldWidth inputs ≤ inputs := by
  have slopeLe : parameters.blockWidth ≤ parameters.prefixSlope := by
    have := parameters.incidenceSlope_le
    omega
  exact (Nat.mul_le_mul_right (parameters.blocks inputs) slopeLe).trans (parameters.prefixWidth_le inputs)

/-- The scheduler depth is no larger than the input length. -/
theorem copyDepth_le (inputs : Nat) : parameters.copyDepth inputs ≤ inputs := by
  have slopeLe : parameters.copySlope ≤ parameters.prefixSlope := by
    have := parameters.incidenceSlope_le
    omega
  exact (Nat.mul_le_mul_right (parameters.blocks inputs) slopeLe).trans (parameters.prefixWidth_le inputs)

/-- Each full block contributes the prescribed number of suffix bits. -/
theorem suffixWidth_lower (inputs : Nat) : parameters.suffixSlope * parameters.blocks inputs ≤ parameters.suffixWidth inputs := by
  have blockFits : parameters.inputSlope * parameters.blocks inputs ≤ inputs := by
    simpa only [blocks, Nat.mul_comm] using Nat.div_mul_le_self inputs parameters.inputSlope
  have split := Nat.sub_add_cancel parameters.splitPositive.le
  have splitScaled := congrArg (fun slope => slope * parameters.blocks inputs) split
  have inputSplit := parameters.prefix_add_suffix inputs
  change parameters.suffixSlope + parameters.prefixSlope = parameters.inputSlope at split
  change (parameters.suffixSlope + parameters.prefixSlope) * parameters.blocks inputs =
    parameters.inputSlope * parameters.blocks inputs at splitScaled
  change parameters.prefixSlope * parameters.blocks inputs + parameters.suffixWidth inputs = inputs at inputSplit
  nlinarith

/-- The block count itself is a lower bound on the suffix length. -/
theorem blocks_le_suffixWidth (inputs : Nat) : parameters.blocks inputs ≤ parameters.suffixWidth inputs := by
  have positive := parameters.suffixSlope_positive
  have bound := parameters.suffixWidth_lower inputs
  nlinarith

/-- Putting the incomplete block into the suffix preserves the desired
suffix/input fraction without any rounding loss in the leading coefficient. -/
theorem suffixFraction (inputs : Nat) :
    parameters.suffixSlope * inputs ≤ parameters.inputSlope * parameters.suffixWidth inputs := by
  have blockFits : parameters.inputSlope * parameters.blocks inputs ≤ inputs := by
    simpa only [blocks, Nat.mul_comm] using Nat.div_mul_le_self inputs parameters.inputSlope
  have scaledBlocks := Nat.mul_le_mul_left parameters.prefixSlope blockFits
  have split : parameters.suffixSlope + parameters.prefixSlope = parameters.inputSlope :=
    Nat.sub_add_cancel parameters.splitPositive.le
  have slopeScaled := congrArg (fun slope => slope * inputs) split
  have inputScaled := congrArg (fun count => parameters.inputSlope * count) (parameters.prefix_add_suffix inputs)
  change parameters.inputSlope * (parameters.prefixSlope * parameters.blocks inputs + parameters.suffixWidth inputs) =
    parameters.inputSlope * inputs at inputScaled
  nlinarith

/-- A fixed block-count cutoff makes the scheduler's batch cover every
copy count allowed by the target rational exponent. -/
theorem copyExponent_le (inputs : Nat)
    (blocksLarge : numerator * parameters.inputSlope ≤ parameters.blocks inputs) :
    numerator * inputs / denominator ≤ parameters.copyDepth inputs := by
  have denominatorPositive : 0 < denominator := by have := parameters.copyRate; nlinarith
  have upper : inputs ≤ parameters.inputSlope * (parameters.blocks inputs + 1) :=
    (Nat.lt_mul_div_succ inputs parameters.inputSlope_positive).le
  have exponentBound : numerator * inputs ≤ parameters.copyDepth inputs * denominator := by
    calc
      _ ≤ numerator * (parameters.inputSlope * (parameters.blocks inputs + 1)) := Nat.mul_le_mul_left _ upper
      _ ≤ (numerator * parameters.inputSlope + 1) * parameters.blocks inputs := by nlinarith
      _ ≤ (denominator * parameters.copySlope) * parameters.blocks inputs :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt parameters.copyRate)
      _ = _ := by unfold copyDepth; ring
  calc
    _ ≤ (parameters.copyDepth inputs * denominator) / denominator := Nat.div_le_div_right exponentBound
    _ = _ := Nat.mul_div_cancel _ denominatorPositive

/-- One further block of slack also covers rounding the rational exponent upward. -/
theorem copyExponent_succ_le (inputs : Nat)
    (blocksLarge : numerator * parameters.inputSlope + 1 ≤ parameters.blocks inputs) :
    numerator * inputs / denominator + 1 ≤ parameters.copyDepth inputs := by
  have denominatorPositive : 0 < denominator := by have := parameters.copyRate; nlinarith
  have upper : inputs ≤ parameters.inputSlope * (parameters.blocks inputs + 1) :=
    (Nat.lt_mul_div_succ inputs parameters.inputSlope_positive).le
  have exponentBound : numerator * inputs < parameters.copyDepth inputs * denominator := by
    calc
      _ ≤ numerator * (parameters.inputSlope * (parameters.blocks inputs + 1)) := Nat.mul_le_mul_left _ upper
      _ < (numerator * parameters.inputSlope + 1) * parameters.blocks inputs := by nlinarith
      _ ≤ (denominator * parameters.copySlope) * parameters.blocks inputs :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt parameters.copyRate)
      _ = _ := by unfold copyDepth; ring
  exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul denominatorPositive).mpr exponentBound)

/-- Nine complete field blocks absorb the fixed scheduler constant `512`. -/
theorem directionBudget (inputs : Nat) (blocksLarge : 9 ≤ parameters.blocks inputs) :
    512 * networkRecords (parameters.copyDepth inputs) * Nat.card (BinaryExtension (parameters.fieldWidth inputs)) ≤
      Nat.card (ℙ (BinaryExtension (parameters.fieldWidth inputs))
        (Fin parameters.dimension → BinaryExtension (parameters.fieldWidth inputs))) := by
  have blocksPositive : 0 < parameters.blocks inputs := by omega
  have widthPositive : 0 < parameters.fieldWidth inputs := Nat.mul_pos parameters.blockPositive blocksPositive
  have scaled := Nat.mul_le_mul_right (parameters.blocks inputs) parameters.directionSlack
  have exponents : 9 + parameters.copyDepth inputs + parameters.fieldWidth inputs ≤
      parameters.fieldWidth inputs * (parameters.dimension - 1) := by
    dsimp [copyDepth, fieldWidth]
    nlinarith
  rw [networkRecords_eq_two_pow, card_binaryExtension widthPositive]
  calc
    _ = 2 ^ (9 + parameters.copyDepth inputs + parameters.fieldWidth inputs) := by
      rw [pow_add, pow_add]
      norm_num
    _ ≤ 2 ^ (parameters.fieldWidth inputs * (parameters.dimension - 1)) := Nat.pow_le_pow_right (by omega) exponents
    _ ≤ _ := CodeParameters.projectiveDirections_lower _ _ parameters.dimensionPositive widthPositive

end Algebraic.MassProduction.Nonuniform.GeometricSlopes
