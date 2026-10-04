/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics

/-!
# Rectangle parameters for the fixed polynomial-time family

These facts concern the existing `sourceReductionHardFamily`, at its full input length.
The threshold doubles the extractor threshold to account for its balanced padding.
They are independent of the circuit basis, so mixed aggregate circuits use exactly the
same family and polynomial-time evaluator as the ordinary binary lower bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open Filter Extractor

/-- The rectangle threshold for the fixed, balanced hard family at the full input length. -/
def familyThreshold (n : Nat) : Nat :=
  2 * 2 ^ sourceReductionEntropy (n - 1) (sourceReductionFamilyScale (n - 1))

theorem familyThreshold_one_lt (n : Nat) : 1 < familyThreshold n := by
  unfold familyThreshold
  have := Nat.two_pow_pos (sourceReductionEntropy (n - 1) (sourceReductionFamilyScale (n - 1)))
  lia

/-- The rectangle threshold has sublinear binary logarithm. -/
theorem familyThreshold_log_isLittleO :
    (fun n => Real.logb 2 (familyThreshold n)) =o[atTop] (fun n => (n : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro δ hδ
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually
    (sourceReductionFamilyEntropy_isLittleO.def (by positivity : 0 < δ / 2)),
    eventually_mul_logb_add_lt 0 1 (by positivity : 0 < δ / 2)] with n small constant
  have entropy : (sourceReductionEntropy (n - 1) (sourceReductionFamilyScale (n - 1)) : ℝ) ≤
      δ / 2 * (n - 1 : Nat) := by
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _)] using small
  have shift : ((n - 1 : Nat) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have entropy' := entropy.trans (mul_le_mul_of_nonneg_left shift (by positivity : 0 ≤ δ / 2))
  have constant' : (1 : ℝ) ≤ δ / 2 * n := by
    simpa only [zero_mul, zero_add] using constant.le
  have logarithm : Real.logb 2 (familyThreshold n) =
      1 + sourceReductionEntropy (n - 1) (sourceReductionFamilyScale (n - 1)) := by
    simp only [familyThreshold, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one]
  rw [logarithm, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  linarith

/-- The fixed family is eventually dense and rectangle-free at the stated threshold. -/
theorem family_eventually_hard :
    ∀ᶠ n in atTop, RectangleFree (sourceReductionHardFamily n) (familyThreshold n) ∧
      2 ^ (n - 2) ≤ (accepting (sourceReductionHardFamily n)).card := by
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually sourceReductionFamily_eventually_flat,
    eventually_ge_atTop 1] with n extract positive
  cases n with
  | zero => lia
  | succ n =>
    simp only [Nat.add_sub_cancel] at extract
    rw [sourceReductionHardFamily_succ]
    refine ⟨?_, ?_⟩
    · exact extract.balancePad_rectangleFree (by positivity) (by norm_num : (35 / 72 : ℝ) < 1 / 2)
    · rw [card_accepting_balancePad]
      exact Nat.pow_le_pow_right (by decide) (by lia)

end Algebraic.Cutwidth.Aggregate
