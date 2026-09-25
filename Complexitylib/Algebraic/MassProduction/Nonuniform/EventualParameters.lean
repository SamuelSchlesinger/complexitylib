/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.LeadingCost
public import Complexitylib.Algebraic.MassProduction.Nonuniform.OverheadPolynomial
public import Complexitylib.Algebraic.MassProduction.Growth

/-!
# Eventual validity and normalized cost of the chosen parameters

Fixed block-count cutoffs supply the code rate, packing precision, synthesis
precision, and direction/copy margins. A single exponential-growth estimate
absorbs the complete seventh-degree runtime overhead after normalization by
the input length.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.CoefficientParameters

open Sorting HighRate Filter
open scoped Topology

variable (parameters : CoefficientParameters numerator denominator precision)

set_option maxHeartbeats 800000

/-- Integral sharp bound used for every shorter resource function. -/
def resourceBound (inputs : Nat) : Nat :=
  ((parameters.resourcePrecision + 1) * 2 ^ parameters.geometry.suffixWidth inputs) /
    (parameters.resourcePrecision * parameters.geometry.suffixWidth inputs)

/-- Exact finite theorem bound at the selected input-length parameters. -/
def totalCost (inputs : Nat) : Nat :=
  FiniteBound.costBound (parameters.geometry.copyDepth inputs) (parameters.geometry.prefixWidth inputs)
    parameters.geometry.dimension parameters.geometry.blockWidth (parameters.geometry.blocks inputs)
    (parameters.geometry.suffixWidth inputs) (parameters.resourceBound inputs)

/-- Numerical and resource-synthesis premises needed to apply the finite
theorem and obtain the target coefficient at one input length. -/
structure Ready (inputs : Nat) : Prop where
  /-- Absorbs the scheduler's fixed constant and ensures positive field width. -/
  blocksLarge : 9 ≤ parameters.geometry.blocks inputs
  /-- The scheduled batch covers the rational exponent rounded upward. -/
  copiesFit : numerator * inputs / denominator + 1 ≤ parameters.geometry.copyDepth inputs
  /-- Every actual shorter Lupanov circuit meets the selected integral bound. -/
  resourcesBounded : ∀ function : ScalarFunction Bool (parameters.geometry.suffixWidth inputs),
    (LupanovSynthesis.lupanovCircuit (parameters.geometry.suffixWidth inputs) function).cost DeMorgan.standardCost ≤
      parameters.resourceBound inputs
  /-- The complete finite cost satisfies the target normalized coefficient. -/
  costBound : precision * (denominator - numerator) * inputs * parameters.totalCost inputs ≤
    (precision + 1) * denominator * 2 ^ inputs

/-- All chosen premises hold eventually, uniformly in the Boolean function
and in the number of requested copies. -/
theorem eventually_ready : ∀ᶠ inputs in atTop, parameters.Ready inputs := by
  let geometry := parameters.geometry
  let q := parameters.resourcePrecision
  obtain ⟨synthesisCutoff, synthesisBound⟩ := LupanovRuntime.normalizedResourceBound q parameters.resourcePositive
  obtain ⟨roundingCutoff, roundingBound⟩ := eventually_atTop.mp
    (Growth.eventually_const_mul_pow_le_two_pow (q * geometry.blockWidth) 1)
  let minimumBlocks := roundingCutoff + q * (2 ^ (geometry.blockWidth * geometry.dimension) - 1) +
    numerator * geometry.inputSlope + synthesisCutoff + 9
  have growth := Growth.eventually_const_mul_pow_le_two_pow_div
    (2 * precision * (denominator - numerator) * OverheadPolynomial.coefficient geometry.dimension) 8
    geometry.inputSlope geometry.inputSlope_positive
  filter_upwards [eventually_ge_atTop (geometry.inputSlope * minimumBlocks), growth] with inputs large polynomial
  have blocksLarge : minimumBlocks ≤ geometry.blocks inputs := by
    apply (Nat.le_div_iff_mul_le geometry.inputSlope_positive).mpr
    simpa only [Nat.mul_comm] using large
  have nineBlocks : 9 ≤ geometry.blocks inputs := by dsimp [minimumBlocks] at blocksLarge; omega
  have blocksPositive : 0 < geometry.blocks inputs := by omega
  have inputsPositive : 1 ≤ inputs := by
    have small := Nat.div_le_self inputs geometry.inputSlope
    change geometry.blocks inputs ≤ inputs at small
    omega
  have rateBlocks : q * (2 ^ (geometry.blockWidth * geometry.dimension) - 1) ≤ geometry.blocks inputs := by
    dsimp [minimumBlocks] at blocksLarge
    omega
  have roundingScalar : q * geometry.blockWidth * geometry.blocks inputs ≤ 2 ^ geometry.blocks inputs := by
    have past : roundingCutoff ≤ geometry.blocks inputs := by dsimp [minimumBlocks] at blocksLarge; omega
    simpa only [pow_one] using roundingBound _ past
  have roundingSmall : q * (2 ^ (geometry.dimension * (geometry.blockWidth * geometry.blocks inputs)) *
      (geometry.blockWidth * geometry.blocks inputs)) ≤ 2 ^ geometry.prefixWidth inputs := by
    calc
      _ = 2 ^ (geometry.dimension * (geometry.blockWidth * geometry.blocks inputs)) *
          (q * geometry.blockWidth * geometry.blocks inputs) := by ring
      _ ≤ 2 ^ (geometry.dimension * (geometry.blockWidth * geometry.blocks inputs)) * 2 ^ geometry.blocks inputs :=
        Nat.mul_le_mul_left _ roundingScalar
      _ = _ := by rw [← pow_add]; congr 1; unfold GeometricSlopes.prefixWidth GeometricSlopes.prefixSlope; ring
  let resources := ResourceLayout.count
    (FiniteBound.copies (geometry.prefixWidth inputs) geometry.dimension geometry.blockWidth (geometry.blocks inputs))
    geometry.dimension (geometry.fieldWidth inputs)
  have storage : q * resources ≤ (q + 2) * 2 ^ geometry.prefixWidth inputs :=
    FiniteBound.resourceCount_le_nearOne blocksPositive rateBlocks roundingSmall
  have resourceBudget : resources ≤ 3 * 2 ^ geometry.prefixWidth inputs := by
    have qPositive : 0 < q := parameters.resourcePositive
    have coefficient : q + 2 ≤ 3 * q := by omega
    have scaled := storage.trans (Nat.mul_le_mul_right (2 ^ geometry.prefixWidth inputs) coefficient)
    nlinarith
  let overhead := RuntimeComposition.overhead (geometry.copyDepth inputs)
    (FiniteBound.copies (geometry.prefixWidth inputs) geometry.dimension geometry.blockWidth (geometry.blocks inputs))
    (geometry.prefixWidth inputs) geometry.dimension (geometry.fieldWidth inputs) (geometry.suffixWidth inputs)
    (FiniteParameters.binaryDepth
      (FiniteBound.copies (geometry.prefixWidth inputs) geometry.dimension geometry.blockWidth (geometry.blocks inputs)))
    (FiniteParameters.binaryDepth (geometry.fieldWidth inputs))
  have overheadBound : overhead ≤ OverheadPolynomial.coefficient geometry.dimension *
      2 ^ geometry.prefixWidth inputs * inputs ^ 7 := by
    apply OverheadPolynomial.overhead_le inputsPositive (geometry.copyDepth_le inputs) (geometry.prefixWidth_le inputs)
      (geometry.fieldWidth_le inputs) (Nat.sub_le _ _)
    · exact (FiniteBound.copies_bitWidth_le _ _ _ _).trans (Nat.add_le_add_right (geometry.prefixWidth_le inputs) 1)
    · exact (FiniteBound.selector_bitWidth_le _).trans (geometry.fieldWidth_le inputs)
    · exact geometry.pointBudget inputs
    · exact resourceBudget
  have runtime : 2 * precision * (denominator - numerator) * inputs * overhead ≤ denominator * 2 ^ inputs := by
    have denominatorPositive : 0 < denominator := by have := geometry.copyRate; nlinarith
    calc
      _ ≤ (2 * precision * (denominator - numerator) * inputs) *
          (OverheadPolynomial.coefficient geometry.dimension * 2 ^ geometry.prefixWidth inputs * inputs ^ 7) :=
        Nat.mul_le_mul_left _ overheadBound
      _ = (2 * precision * (denominator - numerator) * OverheadPolynomial.coefficient geometry.dimension * inputs ^ 8) *
          2 ^ geometry.prefixWidth inputs := by ring
      _ ≤ 2 ^ (inputs / geometry.inputSlope) * 2 ^ geometry.prefixWidth inputs := Nat.mul_le_mul_right _ polynomial
      _ ≤ 2 ^ geometry.suffixWidth inputs * 2 ^ geometry.prefixWidth inputs :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (geometry.blocks_le_suffixWidth inputs))
      _ = 2 ^ inputs := by rw [← pow_add, Nat.add_comm, geometry.prefix_add_suffix]
      _ ≤ _ := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2 ^ inputs) (Nat.succ_le_of_lt denominatorPositive)
  have synthNumeric : q * parameters.resourceBound inputs * geometry.suffixWidth inputs ≤
      (q + 1) * 2 ^ geometry.suffixWidth inputs := by
    have division := Nat.div_mul_le_self ((q + 1) * 2 ^ geometry.suffixWidth inputs) (q * geometry.suffixWidth inputs)
    simpa only [resourceBound, q, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using division
  refine ⟨nineBlocks, geometry.copyExponent_succ_le inputs ?_, ?_, ?_⟩
  · dsimp [minimumBlocks] at blocksLarge
    omega
  · apply synthesisBound
    have past : synthesisCutoff ≤ geometry.blocks inputs := by dsimp [minimumBlocks] at blocksLarge; omega
    exact past.trans (geometry.blocks_le_suffixWidth inputs)
  · exact parameters.cost_le_coefficient (geometry.prefix_add_suffix inputs) (geometry.suffixFraction inputs)
      storage synthNumeric runtime

end Algebraic.MassProduction.Nonuniform.CoefficientParameters
