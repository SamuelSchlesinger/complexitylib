/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.FiniteBound

/-!
# Quantitative storage and key widths for the chosen high-rate code

These inequalities retain the rate-one factor and charge at most one whole
codeword for rounding. They concern exact integer counts and are ready for
eventual parameter estimates.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.FiniteBound

open HighRate

/-- The digit alphabet table is exactly the affine point space. -/
theorem alphabetPower_eq (dimension blockWidth blocks : Nat) :
    (2 ^ (blockWidth * dimension)) ^ blocks = 2 ^ (dimension * (blockWidth * blocks)) := by
  rw [← pow_mul]
  congr 1
  ring

/-- Rate-one storage bound including the one-codeword rounding term. -/
theorem resourceCount_le_rate
    (blocksPositive : 0 < blocks)
    (blocksLarge : precision * (2 ^ (blockWidth * dimension) - 1) ≤ blocks) :
    precision * ResourceLayout.count (copies prefixWidth dimension blockWidth blocks) dimension (blockWidth * blocks) ≤
      (precision + 1) * 2 ^ prefixWidth + precision * (2 ^ (dimension * (blockWidth * blocks)) * (blockWidth * blocks)) := by
  have rate := retainedDimension_rate (2 ^ (blockWidth * dimension)) blocks precision
    (by positivity) blocksPositive blocksLarge
  rw [alphabetPower_eq] at rate
  have bound := packingCopies_storage (2 ^ prefixWidth)
    (retainedDimension (2 ^ (blockWidth * dimension)) blocks)
    (2 ^ (dimension * (blockWidth * blocks))) (blockWidth * blocks) precision rate
  simpa only [ResourceLayout.count, copies, Nat.mul_assoc] using bound

/-- If one codeword is negligible at the selected precision, the complete
bank has expansion at most `(precision+2)/precision`. -/
theorem resourceCount_le_nearOne
    (blocksPositive : 0 < blocks)
    (blocksLarge : precision * (2 ^ (blockWidth * dimension) - 1) ≤ blocks)
    (roundingSmall : precision * (2 ^ (dimension * (blockWidth * blocks)) * (blockWidth * blocks)) ≤ 2 ^ prefixWidth) :
    precision * ResourceLayout.count (copies prefixWidth dimension blockWidth blocks) dimension (blockWidth * blocks) ≤
      (precision + 2) * 2 ^ prefixWidth := by
  have bound := resourceCount_le_rate (prefixWidth := prefixWidth) blocksPositive blocksLarge
  nlinarith

/-- Copy-index keys use at most one bit more than the source prefix. -/
theorem copies_bitWidth_le (prefixWidth dimension blockWidth blocks : Nat) :
    FiniteParameters.binaryDepth (copies prefixWidth dimension blockWidth blocks) ≤ prefixWidth + 1 := by
  have tablePositive : 1 ≤ 2 ^ prefixWidth := Nat.one_le_pow _ _ (by omega)
  apply FiniteParameters.binaryDepth_le
  unfold copies packingCopies
  have quotient := Nat.div_le_self (2 ^ prefixWidth)
    (retainedDimension (2 ^ (blockWidth * dimension)) blocks * (blockWidth * blocks))
  rw [pow_succ]
  omega

/-- A field-basis selector fits in at most the field symbol's bit width. -/
theorem selector_bitWidth_le (width : Nat) : FiniteParameters.binaryDepth width ≤ width :=
  FiniteParameters.binaryDepth_le width width (Nat.le_of_lt (@Nat.lt_pow_self width 2 (by omega)))

end Algebraic.MassProduction.Nonuniform.FiniteBound
