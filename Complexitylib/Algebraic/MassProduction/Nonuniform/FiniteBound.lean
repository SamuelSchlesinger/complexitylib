/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.LupanovRuntime
public import Complexitylib.Algebraic.MassProduction.HighRate.CodePacking

/-!
# A fully instantiated finite high-rate mass-production bound

The systematic code, source-bit placement, routing index widths, scheduler,
and resource circuits are all constructed by proved existence theorems.
Only finite numerical parameter conditions remain: positive field blocks,
enough digit bits for the dimension, and the projective-direction budget.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.FiniteBound

open Sorting HighRate RuntimePipeline
open scoped LinearAlgebra.Projectivization

/-- Quotient-plus-one number of code copies needed by the source table. -/
def copies (prefixWidth dimension blockWidth blocks : Nat) : Nat :=
  packingCopies (2 ^ prefixWidth) (retainedDimension (2 ^ (blockWidth * dimension)) blocks) (blockWidth * blocks)

/-- Canonically chosen routing widths and the exact finite evaluation bound. -/
def costBound (depth prefixWidth dimension blockWidth blocks suffixWidth resourceBound : Nat) : Nat :=
  let width := blockWidth * blocks
  let codeCopies := copies prefixWidth dimension blockWidth blocks
  RuntimeComposition.overhead depth codeCopies prefixWidth dimension width suffixWidth
    (FiniteParameters.binaryDepth codeCopies) (FiniteParameters.binaryDepth width) +
  ResourceLayout.count codeCopies dimension width * resourceBound

/-- Complete finite mass production under numerical parameter hypotheses,
using any uniform bound on the actual shorter Lupanov resource circuits. -/
theorem booleanMassComplexity_le
    (blockPositive : 0 < blockWidth) (blocksPositive : 0 < blocks) (dimensionPositive : 0 < dimension)
    (dimensionFits : dimension ≤ 2 ^ blockWidth)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension (blockWidth * blocks)) ≤
      Nat.card (ℙ (BinaryExtension (blockWidth * blocks)) (Fin dimension → BinaryExtension (blockWidth * blocks))))
    (function : Fin (2 ^ prefixWidth) → (Fin suffixWidth → Bool) → Bool)
    (resourceBounded : ∀ resourceFunction : ScalarFunction Bool suffixWidth,
      (LupanovSynthesis.lupanovCircuit suffixWidth resourceFunction).cost DeMorgan.standardCost ≤ resourceBound) :
    booleanMassComplexity (requestFunction function) (networkRecords depth) ≤
      (costBound depth prefixWidth dimension blockWidth blocks suffixWidth resourceBound : Nat) := by
  obtain ⟨code, _, ⟨placement⟩⟩ := existsBinaryCodeAndPlacement blockWidth blocks dimension prefixWidth
    blockPositive blocksPositive dimensionPositive dimensionFits
  exact LupanovRuntime.booleanMassComplexity_le_of_resourceBound (Nat.mul_pos blockPositive blocksPositive)
    dimensionPositive budget code placement function
    (Nat.le_pow_clog (by omega : 1 < 2) _) (Nat.le_pow_clog (by omega : 1 < 2) _) resourceBounded

/-- An unconditional finite resource envelope also gives a bound at every
suffix width, before any eventual sharp-synthesis estimate is invoked. -/
theorem booleanMassComplexity_le_explicit
    (blockPositive : 0 < blockWidth) (blocksPositive : 0 < blocks) (dimensionPositive : 0 < dimension)
    (dimensionFits : dimension ≤ 2 ^ blockWidth)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension (blockWidth * blocks)) ≤
      Nat.card (ℙ (BinaryExtension (blockWidth * blocks)) (Fin dimension → BinaryExtension (blockWidth * blocks))))
    (function : Fin (2 ^ prefixWidth) → (Fin suffixWidth → Bool) → Bool) :
    booleanMassComplexity (requestFunction function) (networkRecords depth) ≤
      (costBound depth prefixWidth dimension blockWidth blocks suffixWidth (LupanovRuntime.resourceCost suffixWidth) : Nat) :=
  booleanMassComplexity_le blockPositive blocksPositive dimensionPositive dimensionFits budget function
    (LupanovSynthesis.lupanovCircuit_cost_le suffixWidth)

end Algebraic.MassProduction.Nonuniform.FiniteBound
