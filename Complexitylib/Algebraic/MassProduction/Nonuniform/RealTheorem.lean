/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RealParameters

/-!
# The manuscript's sharp theorem for real copy rates

For every real `0 <= gamma < 1` and every positive additive error, one
cutoff works for all input functions and all positive integer copy counts
at most `2^(gamma*n)`. The conclusion supplies a finite natural cost bound,
so no conversion of infinite circuit complexity to a real number is used.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open Filter

/-- The sharp leading coefficient with the manuscript's real-rate and
additive-error quantifiers, witnessed by an actual finite cost bound. -/
def RealSharpMassProduction : Prop :=
  ∀ gamma : Real, 0 ≤ gamma → gamma < 1 →
    ∀ epsilon : Real, 0 < epsilon → ∃ cutoff : Nat,
      ∀ inputs : Nat, cutoff ≤ inputs →
        ∀ (function : ScalarFunction Bool inputs) (copies : Nat),
          0 < copies → (copies : Real) ≤ (2 : Real) ^ (gamma * inputs) →
            ∃ bound : Nat, booleanMassComplexity function copies ≤ (bound : Nat) ∧
              (bound : Real) ≤ (1 / (1 - gamma) + epsilon) * ((2 : Real) ^ inputs / inputs)

/-- Both the improved coefficient and the full real exponential copy range
hold for complete De Morgan circuits on the original disjoint input blocks. -/
theorem realSharpMassProduction : RealSharpMassProduction := by
  intro gamma nonnegative proper epsilon errorPositive
  obtain ⟨numerator, denominator, precision, fractionProper, precisionPositive, rateBound, coefficientBound⟩ :=
    existsRealCoefficientParameters nonnegative proper errorPositive
  obtain ⟨parameters⟩ := existsCoefficientParameters fractionProper precisionPositive
  obtain ⟨cutoff, pastCutoff⟩ := eventually_atTop.mp parameters.eventually_ready
  refine ⟨max cutoff 1, ?_⟩
  intro inputs large function copies copiesPositive copiesBound
  have inputsPositive : 0 < inputs := by omega
  have denominatorPositive : 0 < denominator := by omega
  have ready := pastCutoff inputs (by omega)
  have rounded := realCopyBudget_le denominatorPositive rateBound.le copiesBound
  refine ⟨parameters.totalCost inputs, ready.booleanMassComplexity_le function copies copiesPositive rounded, ?_⟩
  have finite : (precision : Real) * ((denominator - numerator : Nat) : Real) * inputs * parameters.totalCost inputs ≤
      ((precision : Real) + 1) * denominator * (2 : Real) ^ inputs := by exact_mod_cast ready.costBound
  have scaled := mul_le_mul_of_nonneg_right coefficientBound (pow_nonneg (by norm_num : (0 : Real) ≤ 2) inputs)
  have positiveScale : 0 < (precision : Real) * ((denominator - numerator : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos precisionPositive (Nat.sub_pos_iff_lt.mpr fractionProper)
  have normalized : (inputs : Real) * parameters.totalCost inputs ≤
      (1 / (1 - gamma) + epsilon) * (2 : Real) ^ inputs := by
    apply (mul_le_mul_iff_right₀ positiveScale).mp
    calc
      _ = (precision : Real) * ((denominator - numerator : Nat) : Real) * inputs * parameters.totalCost inputs := by ring
      _ ≤ _ := finite.trans scaled
      _ = _ := by ring
  have inputsRealPositive : (0 : Real) < inputs := by exact_mod_cast inputsPositive
  rw [← mul_div_assoc]
  apply (le_div_iff₀ inputsRealPositive).mpr
  simpa only [mul_comm (inputs : Real) (parameters.totalCost inputs : Real)] using normalized

end Algebraic.MassProduction.Nonuniform
