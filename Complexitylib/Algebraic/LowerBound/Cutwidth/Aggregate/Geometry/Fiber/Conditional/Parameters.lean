/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Parameters

/-!
# Exact constants for entropy conditioned on majority fibers

On a product of three-point pair fibers, two and three distinct prescribed
coordinates have probabilities at most `4/9` and `8/27`. Their binary entropy
savings determine positive interpolation weights for the scalar and inversion
bounds. All comparisons below use exact logarithms and integer inequalities.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

/-- Saving of a two-coordinate conjunction under the majority-product law. -/
noncomputable def pairSaving : ℝ := 1 - Real.binEntropy (4 / 9) / Real.log 2

/-- Saving of a three-coordinate conjunction under the majority-product law. -/
noncomputable def tripleSaving : ℝ := 1 - Real.binEntropy (8 / 27) / Real.log 2

/-- Denominator in the weight of the conditional-majority inequality. -/
noncomputable def fiberDenominator : ℝ := 2 * (messageLoss - pairSaving) - tripleSaving

/-- Weight of the conditional-majority inequality. -/
noncomputable def fiberWeight : ℝ := Shared.wideSaving / fiberDenominator

/-- Weight of the shared-control affine inequality. -/
noncomputable def wideWeight : ℝ := 2 * (messageLoss - pairSaving) * fiberWeight

/-- Narrow-gate saving supplied by the marginal/joint entropy interpolation. -/
noncomputable def effectiveSaving : ℝ := fiberWeight * (messageLoss - 2 * pairSaving)

/-- Weight of the separate-coordinate entropy inequality. -/
noncomputable def separateWeight : ℝ :=
  (Joint.gateSaving - effectiveSaving) / (Joint.gateSaving - Entropy.bitSaving)

/-- Weight of the joint-message entropy inequality. -/
noncomputable def jointWeight : ℝ := 1 - separateWeight

/-- Numerator of the conditional-majority scalar coefficient. -/
noncomputable def scalarNumerator : ℝ :=
  1 + Entropy.bitSaving / 2 + fiberWeight * (1 + 7 * messageLoss / 2 - 3 * pairSaving)

/-- Denominator of the conditional-majority scalar coefficient. -/
noncomputable def scalarDenominator : ℝ :=
  1 + fiberWeight * (1 + 2 * messageLoss - 2 * pairSaving)

/-- Exact scalar coefficient of the conditional-majority combination. -/
noncomputable def gateCoefficient : ℝ := scalarNumerator / scalarDenominator

/-- Numerator when independent nonaffine output components are counted. -/
noncomputable def inversionNumerator : ℝ :=
  3 + Entropy.bitSaving / 2 + fiberWeight * (3 + 7 * messageLoss / 2 - 3 * pairSaving)

/-- Denominator when independent nonaffine output components are counted. -/
noncomputable def inversionDenominator : ℝ :=
  2 + fiberWeight * (2 + 2 * messageLoss - 2 * pairSaving)

/-- Exact inversion coefficient of the conditional-majority combination. -/
noncomputable def inversionCoefficient : ℝ := inversionNumerator / inversionDenominator

/-- Loss when simultaneous affine inversion outputs live on at most four points. -/
noncomputable def inversionPenalty : ℝ := 4 * wideWeight / inversionDenominator

/-- Exact logarithmic form of the conditional two-coordinate saving. -/
theorem pairSaving_eq : pairSaving =
    17 / 9 - 2 * (Real.log 3 / Real.log 2) + 5 / 9 * (Real.log 5 / Real.log 2) := by
  have log4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have log9 : Real.log 9 = 2 * Real.log 3 := by
    calc
      Real.log 9 = Real.log ((3 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have entropy : Real.binEntropy (4 / 9) =
      2 * Real.log 3 - 8 / 9 * Real.log 2 - 5 / 9 * Real.log 5 := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num [Real.negMulLog_def, Real.log_div, log4, log9]
    ring
  rw [pairSaving, entropy]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

/-- Exact logarithmic form of the conditional three-coordinate saving. -/
theorem tripleSaving_eq : tripleSaving =
    17 / 9 - 3 * (Real.log 3 / Real.log 2) + 19 / 27 * (Real.log 19 / Real.log 2) := by
  have log8 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have log27 : Real.log 27 = 3 * Real.log 3 := by
    calc
      Real.log 27 = Real.log ((3 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have entropy : Real.binEntropy (8 / 27) =
      3 * Real.log 3 - 8 / 9 * Real.log 2 - 19 / 27 * Real.log 19 := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num [Real.negMulLog_def, Real.log_div, log8, log27]
    ring
  rw [tripleSaving, entropy]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

/-- The conditional pair is not unbiased, so its saving is positive. -/
theorem pairSaving_pos : 0 < pairSaving := by
  have less : Real.binEntropy (4 / 9) / Real.log 2 < 1 := by
    rw [div_lt_one (Real.log_pos (by norm_num))]
    exact Real.binEntropy_lt_log_two.mpr (by norm_num)
  unfold pairSaving
  linarith

/-- The conditional triple is not unbiased, so its saving is positive. -/
theorem tripleSaving_pos : 0 < tripleSaving := by
  have less : Real.binEntropy (8 / 27) / Real.log 2 < 1 := by
    rw [div_lt_one (Real.log_pos (by norm_num))]
    exact Real.binEntropy_lt_log_two.mpr (by norm_num)
  unfold tripleSaving
  linarith

/-- The conditional pair saving is nonnegative. -/
theorem pairSaving_nonneg : 0 ≤ pairSaving := pairSaving_pos.le

/-- The conditional triple saving is nonnegative. -/
theorem tripleSaving_nonneg : 0 ≤ tripleSaving := tripleSaving_pos.le

/-- A rational upper bound proved by an exact integer-power comparison. -/
theorem pairSaving_lt : pairSaving < 1 / 64 := by
  have compare : Real.log ((2 : ℝ) ^ 1079 * 5 ^ 320) < Real.log ((3 : ℝ) ^ 1152) :=
    Real.log_lt_log (by positivity) (by
      set_option exponentiation.threshold 1200 in
      norm_num)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at compare
  norm_num only [Nat.cast_ofNat] at compare
  have scaled := (div_lt_div_iff_of_pos_right
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr compare
  rw [pairSaving_eq]
  field_simp at scaled ⊢
  linarith

/-- A rational upper bound proved by an exact integer-power comparison. -/
theorem tripleSaving_lt : tripleSaving < 1 / 8 := by
  have compare : Real.log ((2 : ℝ) ^ 381 * 19 ^ 152) < Real.log ((3 : ℝ) ^ 648) :=
    Real.log_lt_log (by positivity) (by
      set_option exponentiation.threshold 700 in
      norm_num)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at compare
  norm_num only [Nat.cast_ofNat] at compare
  have scaled := (div_lt_div_iff_of_pos_right
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr compare
  rw [tripleSaving_eq]
  field_simp at scaled ⊢
  linarith

/-- Exact rational bounds on the majority message loss. -/
theorem messageLoss_bounds : 7 / 12 < messageLoss ∧ messageLoss < 3 / 5 := by
  have low : Real.log ((2 : ℝ) ^ 19) < Real.log ((3 : ℝ) ^ 12) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have high : Real.log ((3 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at low high
  norm_num only [Nat.cast_ofNat] at low high
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have lower := (div_lt_div_iff_of_pos_right logpos).mpr low
  have upper := (div_lt_div_iff_of_pos_right logpos).mpr high
  rw [messageLoss_eq_logb_three_sub_one, Real.logb]
  field_simp at lower upper ⊢
  constructor <;> linarith

/-- The conditional pair charge leaves a positive majority-fiber saving. -/
theorem pairSaving_lt_messageLoss : pairSaving < messageLoss := by
  linarith [pairSaving_lt, messageLoss_bounds.1]

/-- Exact rational bounds on the unconditional wide-conjunction saving. -/
theorem wideSaving_bounds : 9 / 20 < Shared.wideSaving ∧ Shared.wideSaving < 1 / 2 := by
  have low : Real.log ((2 : ℝ) ^ 14) < Real.log ((7 : ℝ) ^ 5) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have high : Real.log ((7 : ℝ) ^ 7) < Real.log ((2 : ℝ) ^ 20) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at low high
  norm_num only [Nat.cast_ofNat] at low high
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have lower := (div_lt_div_iff_of_pos_right logpos).mpr low
  have upper := (div_lt_div_iff_of_pos_right logpos).mpr high
  rw [Shared.wideSaving, Shared.wideEntropy_eq]
  field_simp at lower upper ⊢
  constructor <;> linarith

/-- The conditional-fiber denominator lies in a positive rational interval. -/
theorem fiberDenominator_bounds : 1 < fiberDenominator ∧ fiberDenominator < 6 / 5 := by
  unfold fiberDenominator
  constructor <;> linarith [messageLoss_bounds.1, messageLoss_bounds.2,
    pairSaving_pos, pairSaving_lt, tripleSaving_pos, tripleSaving_lt]

/-- The conditional-fiber denominator is positive. -/
theorem fiberDenominator_pos : 0 < fiberDenominator := by
  linarith [fiberDenominator_bounds.1]

/-- The conditional-fiber weight lies in a useful exact rational interval. -/
theorem fiberWeight_bounds : 3 / 8 < fiberWeight ∧ fiberWeight < 1 / 2 := by
  unfold fiberWeight
  constructor
  · rw [lt_div_iff₀ fiberDenominator_pos]
    linarith [wideSaving_bounds.1, fiberDenominator_bounds.2]
  · rw [div_lt_iff₀ fiberDenominator_pos]
    linarith [wideSaving_bounds.2, fiberDenominator_bounds.1]

/-- The conditional-fiber inequality has positive weight. -/
theorem fiberWeight_pos : 0 < fiberWeight := by
  linarith [fiberWeight_bounds.1]

/-- The effective saving is between one fifth and three tenths. -/
theorem effectiveSaving_bounds : 1 / 5 < effectiveSaving ∧ effectiveSaving < 3 / 10 := by
  have low : 53 / 96 < messageLoss - 2 * pairSaving := by
    linarith [messageLoss_bounds.1, pairSaving_lt]
  have high : messageLoss - 2 * pairSaving < 3 / 5 := by
    linarith [messageLoss_bounds.2, pairSaving_pos]
  unfold effectiveSaving
  constructor
  · nlinarith [mul_pos (sub_pos.mpr fiberWeight_bounds.1) (sub_pos.mpr low)]
  · nlinarith [mul_pos (sub_pos.mpr fiberWeight_bounds.2) (sub_pos.mpr high)]

/-- The effective saving lies strictly between the two available entropy charges. -/
theorem effectiveSaving_between :
    Entropy.bitSaving < effectiveSaving ∧ effectiveSaving < Joint.gateSaving := by
  have small : Entropy.bitSaving < 1 / 5 := by
    have high := messageLoss_bounds.2
    rw [messageLoss_eq_logb_three_sub_one, Real.logb] at high
    rw [Entropy.bitSaving_eq, ← Joint.quarterEntropy, Joint.quarterEntropy_eq]
    linarith
  have total : Entropy.bitSaving + Joint.gateSaving = 1 / 2 := by
    rw [Entropy.bitSaving_eq, ← Joint.quarterEntropy]
    unfold Joint.gateSaving
    ring
  constructor <;> linarith [effectiveSaving_bounds.1, effectiveSaving_bounds.2]

/-- The shared-control affine inequality has positive weight. -/
theorem wideWeight_pos : 0 < wideWeight := by
  unfold wideWeight
  apply mul_pos _ fiberWeight_pos
  linarith [messageLoss_bounds.1, pairSaving_lt]

/-- The separate-coordinate entropy inequality has positive weight. -/
theorem separateWeight_pos : 0 < separateWeight :=
  div_pos (sub_pos.mpr effectiveSaving_between.2) Fiber.savingGap_pos

/-- The joint entropy weight in a symmetric quotient form. -/
theorem jointWeight_eq : jointWeight =
    (effectiveSaving - Entropy.bitSaving) / (Joint.gateSaving - Entropy.bitSaving) := by
  unfold jointWeight separateWeight
  field_simp [Fiber.savingGap_pos.ne']
  ring

/-- The joint-message entropy inequality has positive weight. -/
theorem jointWeight_pos : 0 < jointWeight := by
  rw [jointWeight_eq]
  exact div_pos (sub_pos.mpr effectiveSaving_between.1) Fiber.savingGap_pos

/-- The unconditional entropy inequalities are combined convexly. -/
theorem separateWeight_add_jointWeight : separateWeight + jointWeight = 1 := by
  unfold jointWeight
  ring

/-- The unconditional narrow-gate charge is exactly the effective saving. -/
theorem weighted_saving :
    separateWeight * Entropy.bitSaving + jointWeight * Joint.gateSaving = effectiveSaving := by
  rw [jointWeight_eq]
  unfold separateWeight
  field_simp [Fiber.savingGap_pos.ne']
  ring

/-- The interpolated overlap charge in terms of the effective saving. -/
theorem jointWeight_mul_overlapPenalty :
    jointWeight * Joint.overlapPenalty = (effectiveSaving - Entropy.bitSaving) / 2 := by
  rw [jointWeight_eq, Fiber.savingGap_eq_two_mul_overlapPenalty]
  field_simp [Joint.overlapPenalty_pos.ne']

/-- The defining conditional-fiber denominator cancels against its weight. -/
theorem fiberWeight_mul_denominator : fiberWeight * fiberDenominator = Shared.wideSaving := by
  unfold fiberWeight
  exact div_mul_cancel₀ _ fiberDenominator_pos.ne'

/-- Conditional wide-gate information supplements the original wide-gate charge. -/
theorem wideWeight_eq : wideWeight = Shared.wideSaving + fiberWeight * tripleSaving := by
  have cancel := fiberWeight_mul_denominator
  unfold fiberDenominator at cancel
  unfold wideWeight
  nlinarith only [cancel]

/-- Unconditional and conditional narrow-gate charges match the affine weight. -/
theorem effectiveSaving_add_pairSaving :
    effectiveSaving + fiberWeight * pairSaving = wideWeight / 2 := by
  unfold effectiveSaving wideWeight
  ring

/-- The combined narrow-gate charge is the shared-control affine weight. -/
theorem effectiveSaving_add_messageLoss :
    effectiveSaving + fiberWeight * messageLoss = wideWeight := by
  unfold effectiveSaving wideWeight
  ring

/-- The matching loss in the conditional majority inequality cancels the affine gain. -/
theorem fiberWeight_mul_pairLoss :
    fiberWeight * (2 * (messageLoss - pairSaving)) = wideWeight := by
  unfold wideWeight
  ring

/-- The scalar denominator is the sum of the three positive inequality weights. -/
theorem scalarDenominator_eq : scalarDenominator = 1 + fiberWeight + wideWeight := by
  unfold scalarDenominator wideWeight
  ring

/-- The scalar denominator is positive. -/
theorem scalarDenominator_pos : 0 < scalarDenominator := by
  rw [scalarDenominator_eq]
  linarith [fiberWeight_pos, wideWeight_pos]

/-- The scalar numerator in the form obtained by adding the finite inequalities. -/
theorem scalarNumerator_eq :
    scalarNumerator = 1 - jointWeight * Joint.overlapPenalty + fiberWeight + 2 * wideWeight := by
  rw [jointWeight_mul_overlapPenalty]
  unfold scalarNumerator effectiveSaving wideWeight
  ring

/-- The inversion denominator is the sum of the rank-adjusted inequality weights. -/
theorem inversionDenominator_eq : inversionDenominator = 2 + 2 * fiberWeight + wideWeight := by
  unfold inversionDenominator wideWeight
  ring

/-- The inversion denominator is positive. -/
theorem inversionDenominator_pos : 0 < inversionDenominator := by
  rw [inversionDenominator_eq]
  linarith [fiberWeight_pos, wideWeight_pos]

/-- The inversion numerator in the form obtained by adding the finite inequalities. -/
theorem inversionNumerator_eq : inversionNumerator =
    3 - jointWeight * Joint.overlapPenalty + 3 * fiberWeight + 2 * wideWeight := by
  rw [jointWeight_mul_overlapPenalty]
  unfold inversionNumerator effectiveSaving wideWeight
  ring

/-- The conditional-majority scalar coefficient exceeds one. -/
theorem one_lt_gateCoefficient : 1 < gateCoefficient := by
  rw [gateCoefficient, lt_div_iff₀ scalarDenominator_pos]
  unfold scalarNumerator scalarDenominator
  nlinarith [Entropy.bitSaving_pos,
    mul_pos fiberWeight_pos Fiber.messageLoss_pos,
    mul_pos fiberWeight_pos (sub_pos.mpr pairSaving_lt_messageLoss)]

/-- The conditional-majority inversion coefficient exceeds three halves. -/
theorem three_halves_lt_inversionCoefficient : (3 / 2 : ℝ) < inversionCoefficient := by
  rw [inversionCoefficient, lt_div_iff₀ inversionDenominator_pos]
  unfold inversionNumerator inversionDenominator
  nlinarith [Entropy.bitSaving_pos, mul_pos fiberWeight_pos Fiber.messageLoss_pos]

/-- The finite inversion penalty is positive. -/
theorem inversionPenalty_pos : 0 < inversionPenalty :=
  div_pos (mul_pos (by norm_num) wideWeight_pos) inversionDenominator_pos

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional
