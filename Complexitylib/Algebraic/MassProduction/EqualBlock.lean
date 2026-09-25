/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.EqualBlockFiniteStep
public import Complexitylib.Algebraic.MassProduction.InputSplit
public import Complexitylib.Algebraic.MassProduction.Padding

/-!
# Exact parameters for the equal-block induction

This module assembles the two-block base case of the fixed-exponent induction.
Rates remain natural fractions, block lengths remain integral, and all floor
and ceiling operations are explicit.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace EqualBlock

open CodeParameters

/-! ## Padding arbitrary lengths to the next even length -/

/-- Ceiling of half the input width, used as the common padded block width. -/
def halfCeil (inputWidth : Nat) : Nat :=
  inputWidth ⌈/⌉ 2

/-- The least even width represented as two copies of `halfCeil`. -/
def nextEvenWidth (inputWidth : Nat) : Nat :=
  halfCeil inputWidth + halfCeil inputWidth

theorem inputWidth_le_nextEvenWidth (inputWidth : Nat) :
    inputWidth <= nextEvenWidth inputWidth := by
  have capacity : inputWidth <= 2 * (inputWidth ⌈/⌉ 2) :=
    (ceilDiv_le_iff_le_mul (by omega : 0 < 2)).mp le_rfl
  unfold nextEvenWidth halfCeil
  omega

theorem nextEvenWidth_le_add_two (inputWidth : Nat) :
    nextEvenWidth inputWidth <= inputWidth + 2 := by
  have ceiling := CodeParameters.ceilDiv_le_div_add_one inputWidth 2
    (by omega)
  have floor := Nat.mul_div_le inputWidth 2
  unfold nextEvenWidth halfCeil
  omega

theorem shannonScale_nextEvenWidth_le
    (inputWidth : Nat)
    (inputPositive : 0 < inputWidth) :
    2 ^ nextEvenWidth inputWidth / nextEvenWidth inputWidth <=
      8 * (2 ^ inputWidth / inputWidth) := by
  simpa only [show 2 * 2 ^ 2 = 8 by norm_num] using
    _root_.Algebraic.MassProduction.shannonScale_le_of_le_add inputWidth
      (nextEvenWidth inputWidth) 2 inputPositive
      (inputWidth_le_nextEvenWidth inputWidth)
      (nextEvenWidth_le_add_two inputWidth)

/-- The complete two-block base case `P₁`: every fixed rational rate below
one half has eventual mass production for arbitrary positive input lengths. -/
theorem massProducesAt_of_rateBelowHalf
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (rateBelowHalf : 2 * numerator < denominator) :
    MassProducesAt numerator denominator := by
  obtain ⟨blockCutoff, blockBound⟩ := Filter.eventually_atTop.1
    (eventually_twoBlock_mass_bound numerator denominator denominatorPositive
      rateBelowHalf)
  refine ⟨8 * twoBlockMassConstant denominator,
    max 1 (2 * blockCutoff), ?_⟩
  intro inputWidth inputPositive pastCutoff function copies copiesPositive
    copiesBound
  let blockWidth := halfCeil inputWidth
  let paddedWidth := nextEvenWidth inputWidth
  have fits : inputWidth <= paddedWidth := inputWidth_le_nextEvenWidth inputWidth
  have paddedWidthEq : paddedWidth = blockWidth + blockWidth := by rfl
  have blockLarge : blockCutoff <= blockWidth := by
    have inputLarge : 2 * blockCutoff <= inputWidth :=
      (le_max_right 1 (2 * blockCutoff)).trans pastCutoff
    have capacity : inputWidth <= 2 * blockWidth := by
      dsimp [blockWidth, halfCeil]
      exact (ceilDiv_le_iff_le_mul (by omega : 0 < 2)).mp le_rfl
    omega
  have paddedCopiesBound : copies <=
      2 ^ (numerator * (blockWidth + blockWidth) / denominator) := by
    have widened := copiesBound.trans
      (rationalCopyBudget_mono_inputs
        (numerator := numerator) (denominator := denominator) fits)
    simpa [rationalCopyBudget, paddedWidthEq] using widened
  let paddedFunction := InputSplit.paddedFunction fits function
  have paddedMass := blockBound blockWidth blockLarge paddedFunction copies
    copiesPositive paddedCopiesBound
  have transport := InputSplit.booleanMassComplexity_le_paddedFunction
    inputPositive fits function copies
  have scaleBound := shannonScale_nextEvenWidth_le inputWidth inputPositive
  calc
    booleanMassComplexity function copies <=
        booleanMassComplexity paddedFunction copies := transport
    _ <= (twoBlockMassConstant denominator *
          (2 ^ (blockWidth + blockWidth) /
            (blockWidth + blockWidth)) : Nat) := paddedMass
    _ = (twoBlockMassConstant denominator *
          (2 ^ paddedWidth / paddedWidth) : Nat) := by
      rw [paddedWidthEq]
    _ <= ((8 * twoBlockMassConstant denominator) *
          (2 ^ inputWidth / inputWidth) : Nat) := by
      exact_mod_cast (calc
        twoBlockMassConstant denominator *
            (2 ^ paddedWidth / paddedWidth) <=
          twoBlockMassConstant denominator *
            (8 * (2 ^ inputWidth / inputWidth)) := by gcongr
        _ = (8 * twoBlockMassConstant denominator) *
            (2 ^ inputWidth / inputWidth) := by ring)

end EqualBlock
end MassProduction
end Algebraic
