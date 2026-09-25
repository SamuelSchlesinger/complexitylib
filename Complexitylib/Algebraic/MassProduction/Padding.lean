/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Growth
public import Complexitylib.Algebraic.MassProduction.InputSplit

/-!
# Padding mass-production bounds

This module packages the generic padding argument used by mass-production
theorems. It compares Shannon scales across a bounded width increase and shows
that every eventual rational-rate bound extends to all positive input lengths.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

/-- A floor-stable comparison of Shannon scales when the larger width adds
at most `padding` variables. -/
theorem shannonScale_le_of_le_add
    (inputWidth targetWidth padding : Nat)
    (inputPositive : 0 < inputWidth)
    (fits : inputWidth <= targetWidth)
    (upper : targetWidth <= inputWidth + padding) :
    2 ^ targetWidth / targetWidth <=
      (2 * 2 ^ padding) * (2 ^ inputWidth / inputWidth) := by
  have powerBound : 2 ^ targetWidth <= 2 ^ padding * 2 ^ inputWidth := by
    calc
      2 ^ targetWidth <= 2 ^ (inputWidth + padding) :=
        Nat.pow_le_pow_right (by omega) upper
      _ = 2 ^ padding * 2 ^ inputWidth := by
        rw [Nat.pow_add]
        ring
  have inputFitsPower : inputWidth <= 2 ^ inputWidth := by
    exact (by omega : inputWidth <= 2 * inputWidth).trans
      (Nat.mul_le_pow (by decide : 2 ≠ 1) inputWidth)
  calc
    2 ^ targetWidth / targetWidth <= 2 ^ targetWidth / inputWidth :=
      Nat.div_le_div_left fits inputPositive
    _ <= (2 ^ padding * 2 ^ inputWidth) / inputWidth :=
      Nat.div_le_div_right powerBound
    _ <= 2 * 2 ^ padding * (2 ^ inputWidth / inputWidth) :=
      Growth.mul_div_le_two_mul_mul_div (2 ^ padding) (2 ^ inputWidth)
        inputWidth inputPositive inputFitsPower

/-- Padding by the fixed cutoff converts an eventual theorem into an
every-positive-length theorem. -/
theorem MassProducesAt.allLengths
    {numerator denominator : Nat}
    (production : MassProducesAt numerator denominator) :
    MassProducesAtAllLengths numerator denominator := by
  obtain ⟨eventualConstant, cutoff, eventualBound⟩ := production
  refine ⟨(2 * 2 ^ cutoff) * eventualConstant, ?_⟩
  intro inputWidth inputPositive function copies copiesPositive copiesBound
  let paddedWidth := inputWidth + cutoff
  have fits : inputWidth <= paddedWidth := by
    dsimp [paddedWidth]
    omega
  have paddedPositive : 0 < paddedWidth := inputPositive.trans_le fits
  have paddedPastCutoff : cutoff <= paddedWidth := by
    dsimp [paddedWidth]
    omega
  have paddedCopiesBound : copies <=
      rationalCopyBudget numerator denominator paddedWidth := by
    exact copiesBound.trans
      (rationalCopyBudget_mono_inputs
        (numerator := numerator) (denominator := denominator) fits)
  let paddedFunction := InputSplit.paddedFunction fits function
  have paddedMass := eventualBound paddedWidth paddedPositive
    paddedPastCutoff paddedFunction copies copiesPositive paddedCopiesBound
  have transport := InputSplit.booleanMassComplexity_le_paddedFunction
    inputPositive fits function copies
  have scaleBound : 2 ^ paddedWidth / paddedWidth <=
      (2 * 2 ^ cutoff) * (2 ^ inputWidth / inputWidth) := by
    apply shannonScale_le_of_le_add inputWidth paddedWidth cutoff inputPositive
      fits
    dsimp [paddedWidth]
    exact le_rfl
  calc
    booleanMassComplexity function copies <=
        booleanMassComplexity paddedFunction copies := transport
    _ <= (eventualConstant *
          (2 ^ paddedWidth / paddedWidth) : Nat) := paddedMass
    _ <= (((2 * 2 ^ cutoff) * eventualConstant) *
          (2 ^ inputWidth / inputWidth) : Nat) := by
      exact_mod_cast (calc
        eventualConstant * (2 ^ paddedWidth / paddedWidth) <=
            eventualConstant * ((2 * 2 ^ cutoff) *
              (2 ^ inputWidth / inputWidth)) := by gcongr
        _ = ((2 * 2 ^ cutoff) * eventualConstant) *
            (2 ^ inputWidth / inputWidth) := by ring)

end MassProduction
end Algebraic
