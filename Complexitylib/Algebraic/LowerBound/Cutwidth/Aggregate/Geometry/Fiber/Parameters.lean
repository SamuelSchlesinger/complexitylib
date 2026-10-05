/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Parameters

/-!
# Exact constants for majority-fiber and entropy combinations

The separate-coordinate and joint-message inequalities are combined so that
their two-variable saving is half the wide-conjunction saving. The additional
majority-fiber inequality has weight `wideSaving / (2 * log₂(3/2))`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

/-- Logarithmic charge in the majority-fiber message inequality. -/
noncomputable def messageLoss : ℝ := Real.logb 2 (3 / 2)

/-- Weight of the majority-fiber inequality. -/
noncomputable def fiberWeight : ℝ := Shared.wideSaving / (2 * messageLoss)

/-- Weight of the separate-coordinate entropy inequality. -/
noncomputable def separateWeight : ℝ :=
  (Joint.gateSaving - Shared.wideSaving / 2) / (Joint.gateSaving - Entropy.bitSaving)

/-- Weight of the joint-message entropy inequality. -/
noncomputable def jointWeight : ℝ :=
  (Shared.wideSaving / 2 - Entropy.bitSaving) / (Joint.gateSaving - Entropy.bitSaving)

/-- Numerator of the scalar gate coefficient. -/
noncomputable def scalarNumerator : ℝ :=
  1 + Entropy.bitSaving / 2 + 7 * Shared.wideSaving / 4 + fiberWeight

/-- Denominator of the scalar gate coefficient. -/
noncomputable def scalarDenominator : ℝ := 1 + Shared.wideSaving + fiberWeight

/-- Exact scalar coefficient supplied by the fiber and entropy combination. -/
noncomputable def gateCoefficient : ℝ := scalarNumerator / scalarDenominator

/-- Numerator when independent nonlinear output components are also counted. -/
noncomputable def inversionNumerator : ℝ :=
  3 + Entropy.bitSaving / 2 + 7 * Shared.wideSaving / 4 + 3 * fiberWeight

/-- Denominator when independent nonlinear output components are also counted. -/
noncomputable def inversionDenominator : ℝ := 2 + Shared.wideSaving + 2 * fiberWeight

/-- Exact coefficient combining component rank, majority fibers, and entropy. -/
noncomputable def inversionCoefficient : ℝ := inversionNumerator / inversionDenominator

/-- Finite loss from the two-dimensional affine restriction. -/
noncomputable def inversionPenalty : ℝ := 4 * Shared.wideSaving / inversionDenominator

/-- The same logarithmic charge in the form supplied by majority-input counting. -/
theorem messageLoss_eq_logb_three_sub_one : messageLoss = Real.logb 2 3 - 1 := by
  rw [messageLoss, Real.logb_div (by norm_num) (by norm_num),
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

/-- The majority-fiber logarithmic charge is positive. -/
theorem messageLoss_pos : 0 < messageLoss := by
  exact Real.logb_pos (by norm_num) (by norm_num)

/-- The majority-fiber inequality has positive weight. -/
theorem fiberWeight_pos : 0 < fiberWeight :=
  div_pos Shared.wideSaving_pos (mul_pos (by norm_num) messageLoss_pos)

/-- The weighted majority-fiber charge is half the wide-conjunction saving. -/
theorem fiberWeight_mul_messageLoss : fiberWeight * messageLoss = Shared.wideSaving / 2 := by
  unfold fiberWeight
  field_simp [messageLoss_pos.ne']

/-- The one-eighth saving exceeds twice the separate two-variable saving. -/
theorem bitSaving_lt_half_wideSaving : Entropy.bitSaving < Shared.wideSaving / 2 := by
  have compare : Real.log ((3 : ℝ) ^ 12) < Real.log ((7 : ℝ) ^ 7) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at compare
  norm_num only [Nat.cast_ofNat] at compare
  have scaled := (div_lt_div_iff_of_pos_right
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr compare
  rw [Entropy.bitSaving_eq, Shared.wideSaving, Shared.wideEntropy_eq,
    ← Joint.quarterEntropy, Joint.quarterEntropy_eq]
  field_simp at scaled ⊢
  linarith

/-- Half the one-eighth saving is less than the joint two-variable saving. -/
theorem half_wideSaving_lt_gateSaving : Shared.wideSaving / 2 < Joint.gateSaving := by
  linarith [Shared.wideSaving_lt_two_mul_gateSaving]

/-- The denominator of the entropy interpolation is positive. -/
theorem savingGap_pos : 0 < Joint.gateSaving - Entropy.bitSaving := by
  linarith [bitSaving_lt_half_wideSaving, half_wideSaving_lt_gateSaving]

/-- The separate-coordinate entropy inequality has positive weight. -/
theorem separateWeight_pos : 0 < separateWeight :=
  div_pos (sub_pos.mpr half_wideSaving_lt_gateSaving) savingGap_pos

/-- The joint-message entropy inequality has positive weight. -/
theorem jointWeight_pos : 0 < jointWeight :=
  div_pos (sub_pos.mpr bitSaving_lt_half_wideSaving) savingGap_pos

/-- The entropy interpolation is a convex combination. -/
theorem separateWeight_add_jointWeight : separateWeight + jointWeight = 1 := by
  unfold separateWeight jointWeight
  field_simp [savingGap_pos.ne']
  ring

/-- The interpolated two-variable saving is half the wide-conjunction saving. -/
theorem weighted_saving :
    separateWeight * Entropy.bitSaving + jointWeight * Joint.gateSaving =
      Shared.wideSaving / 2 := by
  unfold separateWeight jointWeight
  field_simp [savingGap_pos.ne']
  ring

/-- The joint saving gap is exactly twice the overlap penalty. -/
theorem savingGap_eq_two_mul_overlapPenalty :
    Joint.gateSaving - Entropy.bitSaving = 2 * Joint.overlapPenalty := by
  rw [Entropy.bitSaving_eq, ← Joint.quarterEntropy]
  unfold Joint.gateSaving Joint.overlapPenalty
  ring

/-- The overlap charge after entropy interpolation. -/
theorem jointWeight_mul_overlapPenalty :
    jointWeight * Joint.overlapPenalty =
      (Shared.wideSaving / 2 - Entropy.bitSaving) / 2 := by
  unfold jointWeight
  rw [savingGap_eq_two_mul_overlapPenalty]
  field_simp [Joint.overlapPenalty_pos.ne']

/-- The scalar denominator is positive. -/
theorem scalarDenominator_pos : 0 < scalarDenominator := by
  unfold scalarDenominator
  linarith [Shared.wideSaving_pos, fiberWeight_pos]

/-- The component-rank denominator is positive. -/
theorem inversionDenominator_pos : 0 < inversionDenominator := by
  unfold inversionDenominator
  linarith [Shared.wideSaving_pos, fiberWeight_pos]

/-- The scalar coefficient exceeds one. -/
theorem one_lt_gateCoefficient : 1 < gateCoefficient := by
  rw [gateCoefficient, lt_div_iff₀ scalarDenominator_pos]
  unfold scalarNumerator scalarDenominator
  linarith [Entropy.bitSaving_pos, Shared.wideSaving_pos]

/-- The coefficient with independent output components exceeds three halves. -/
theorem three_halves_lt_inversionCoefficient : (3 / 2 : ℝ) < inversionCoefficient := by
  rw [inversionCoefficient, lt_div_iff₀ inversionDenominator_pos]
  unfold inversionNumerator inversionDenominator
  linarith [Entropy.bitSaving_pos, Shared.wideSaving_pos]

/-- The finite component-rank penalty is positive. -/
theorem inversionPenalty_pos : 0 < inversionPenalty :=
  div_pos (mul_pos (by norm_num) Shared.wideSaving_pos) inversionDenominator_pos

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
