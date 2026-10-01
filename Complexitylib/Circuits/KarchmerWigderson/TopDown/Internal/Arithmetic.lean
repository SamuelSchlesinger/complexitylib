/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Arithmetic for the top-down communication exponent

With `C = 32768*194^d`, the choices `epsilon = 1/(32*C)` and
`N = (32*C)^d` turn the finite `16*(C*(m+1))^d ≤ n` obstruction into
an `Omega(n^(1/d))` message lower bound.
-/

public section

namespace Complexity.KarchmerWigderson

theorem finite_budget_of_cost_internal {n d : ℕ} (hd : 0 < d)
    (hlarge : (32 * (32768 * 194 ^ d)) ^ d ≤ n) {m : ℝ} (hm : 0 ≤ m)
    (hcost : m ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (32 * (32768 * (194 : ℝ) ^ d))) :
    16 * (32768 * (194 : ℝ) ^ d * (m + 1)) ^ d ≤ (n : ℝ) := by
  let C : ℝ := 32768 * (194 : ℝ) ^ d
  let r : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlarge' : (32 * C) ^ d ≤ (n : ℝ) := by
    dsimp [C]
    exact_mod_cast hlarge
  have hroot : 32 * C ≤ r := by
    have hh := Real.rpow_le_rpow (show 0 ≤ (32 * C) ^ d by positivity)
      hlarge' (show 0 ≤ (d : ℝ)⁻¹ by positivity)
    rw [Real.pow_rpow_inv_natCast (by positivity) (Nat.ne_of_gt hd)] at hh
    exact hh
  have hcost' : m * (32 * C) ≤ r := (le_div_iff₀ (by positivity)).mp hcost
  have hstep : C * (m + 1) ≤ r / 16 := by nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ C * (m + 1) by positivity) hstep d
  have hrootpow : r ^ d = (n : ℝ) := Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hd)
  rw [div_pow, hrootpow] at hpow
  have hden : (16 : ℝ) ≤ (16 : ℝ) ^ d := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) (Nat.succ_le_of_lt hd)
  have hh : 16 * ((n : ℝ) / (16 : ℝ) ^ d) ≤ n := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.mpr hden)]
  exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hh

end Complexity.KarchmerWigderson
