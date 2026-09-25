/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.SharpTheorem
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real rates and exact integer parameter choices

Rational density and the Archimedean property turn every real rate below
one and positive additive coefficient error into a rational rate and an
integer precision. Rounding the exponent upward covers the real copy budget.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

/-- Real rates and additive errors admit rational/integer parameters with
strict room in both the copy range and the requested coefficient. -/
theorem existsRealCoefficientParameters {gamma epsilon : Real}
    (nonnegative : 0 ≤ gamma) (proper : gamma < 1) (errorPositive : 0 < epsilon) :
    ∃ numerator denominator precision : Nat,
      numerator < denominator ∧ 0 < precision ∧ gamma < (numerator : Real) / denominator ∧
        ((precision : Real) + 1) * denominator ≤
          (1 / (1 - gamma) + epsilon) * precision * ((denominator - numerator : Nat) : Real) := by
  let target := 1 / (1 - gamma) + epsilon
  have gapPositive : 0 < 1 - gamma := by linarith
  obtain ⟨coefficient, lower, upper⟩ := exists_rat_btwn
    (show 1 / (1 - gamma) < target by dsimp [target]; linarith)
  have coefficientPositive : 0 < (coefficient : Real) := (one_div_pos.mpr gapPositive).trans lower
  let rate : Rat := 1 - 1 / coefficient
  have rateValue : (rate : Real) = 1 - 1 / (coefficient : Real) := by simp [rate]
  have rateLower : gamma < (rate : Real) := by
    rw [rateValue]
    have scaled := (div_lt_iff₀ gapPositive).mp lower
    have reciprocal : 1 / (coefficient : Real) < 1 - gamma :=
      (div_lt_iff₀ coefficientPositive).mpr (by nlinarith)
    linarith
  have rateUpper : (rate : Real) < 1 := by rw [rateValue]; have := one_div_pos.mpr coefficientPositive; linarith
  have rateNonnegative : 0 ≤ rate := by exact_mod_cast (nonnegative.trans rateLower.le)
  have numeratorNonnegative : 0 ≤ rate.num := Rat.num_nonneg.mpr rateNonnegative
  have rateFraction : (rate : Real) = (rate.num.toNat : Real) / rate.den := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg numeratorNonnegative).symm
  have denominatorPositive : 0 < (rate.den : Real) := by exact_mod_cast rate.den_pos
  have fractionProper : rate.num.toNat < rate.den := by
    rw [rateFraction] at rateUpper
    have := (div_lt_iff₀ denominatorPositive).mp rateUpper
    exact_mod_cast (by simpa using this : (rate.num.toNat : Real) < rate.den)
  have coefficientIdentity : (coefficient : Real) * ((rate.den - rate.num.toNat : Nat) : Real) = rate.den := by
    rw [Nat.cast_sub fractionProper.le]
    have reciprocal := div_mul_cancel₀ (1 : Real) (ne_of_gt coefficientPositive)
    have fractionIdentity := (eq_div_iff (ne_of_gt denominatorPositive)).mp rateFraction
    rw [rateValue] at fractionIdentity
    nlinarith
  have errorGap : 0 < target - (coefficient : Real) := sub_pos.mpr upper
  obtain ⟨precision, precisionLarge⟩ := exists_nat_gt ((coefficient : Real) / (target - coefficient))
  have precisionPositive : 0 < precision := by
    have positive := div_pos coefficientPositive errorGap
    have : (0 : Real) < precision := positive.trans precisionLarge
    exact_mod_cast this
  have precisionScaled := (div_lt_iff₀ errorGap).mp precisionLarge
  refine ⟨rate.num.toNat, rate.den, precision, fractionProper, precisionPositive, ?_, ?_⟩
  · rwa [← rateFraction]
  · have gapNonnegative : 0 ≤ ((rate.den - rate.num.toNat : Nat) : Real) := Nat.cast_nonneg _
    have leading : ((precision : Real) + 1) * coefficient ≤ target * precision := by nlinarith
    have scaled := mul_le_mul_of_nonneg_right leading gapNonnegative
    calc
      _ = (((precision : Real) + 1) * coefficient) * ((rate.den - rate.num.toNat : Nat) : Real) := by
        rw [mul_assoc, coefficientIdentity]
      _ ≤ _ := scaled
      _ = _ := by rfl

/-- The power of two at the upward-rounded rational exponent covers every
integer copy count allowed by a smaller real exponent. -/
theorem realCopyBudget_le {gamma : Real} {numerator denominator inputs copies : Nat}
    (denominatorPositive : 0 < denominator) (rateBound : gamma ≤ (numerator : Real) / denominator)
    (copiesBound : (copies : Real) ≤ (2 : Real) ^ (gamma * inputs)) :
    copies ≤ 2 ^ (numerator * inputs / denominator + 1) := by
  have positive : 0 < (denominator : Real) := by exact_mod_cast denominatorPositive
  have quotient : (numerator : Real) * inputs <
      ((numerator * inputs / denominator + 1 : Nat) : Real) * denominator := by
    have bound := Nat.lt_mul_div_succ (numerator * inputs) denominatorPositive
    rw [Nat.mul_comm denominator] at bound
    exact_mod_cast bound
  have exponentBound : gamma * inputs ≤ ((numerator * inputs / denominator + 1 : Nat) : Real) := by
    calc
      _ ≤ ((numerator : Real) / denominator) * inputs := mul_le_mul_of_nonneg_right rateBound (Nat.cast_nonneg _)
      _ = ((numerator : Real) * inputs) / denominator := by ring
      _ ≤ _ := ((div_lt_iff₀ positive).mpr quotient).le
  have powerBound := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) exponentBound
  have result := copiesBound.trans powerBound
  rw [Real.rpow_natCast] at result
  exact_mod_cast result

end Algebraic.MassProduction.Nonuniform
