/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Absorbing the logarithmic initial deficit

The middle-layer deficit bound is little-o of every positive power of `n`.
Thus replacing the parity deficit `1` with this logarithmic bound preserves
the exponent `1/(d-1)` in a `d`-round communication lower bound.
-/

public section

namespace Complexity.BooleanAnalysis

open Filter Asymptotics

theorem majorityDeficitBound_eventually_le_internal {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → majorityDeficitBound n ≤ c * (n : ℝ) ^ r := by
  have hlog := isLittleO_log_rpow_atTop hr
  have hconst : (fun _ : ℝ => (130 : ℝ)) =o[atTop] (fun x : ℝ => x ^ r) :=
    Real.isLittleO_const_log_atTop.trans hlog
  have hs := hconst.add (hlog.const_mul_left (Real.log 2)⁻¹)
  have he : ∀ᶠ n : ℕ in atTop,
      ‖(130 : ℝ) + (Real.log 2)⁻¹ * Real.log n‖ ≤ c * ‖(n : ℝ) ^ r‖ :=
    tendsto_natCast_atTop_atTop.eventually (hs.def hc)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hbound := hN n (by omega)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hbound
  have hl : Real.logb 2 (2 * ((n : ℝ) + 1)) ≤ Real.logb 2 (4 * (n : ℝ)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hfour : Real.logb 2 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_mul (by norm_num) (ne_of_gt hnpos), hfour] at hl
  have heq : Real.logb 2 (n : ℝ) = (Real.log 2)⁻¹ * Real.log n := by
    rw [Real.logb, div_eq_mul_inv, mul_comm]
  rw [heq] at hl
  unfold majorityDeficitBound
  exact (show 128 + Real.logb 2 (2 * ((n : ℝ) + 1)) ≤
    130 + (Real.log 2)⁻¹ * Real.log n by linarith).trans ((le_abs_self _).trans hbound)

end Complexity.BooleanAnalysis

namespace Complexity.KarchmerWigderson

theorem finite_budget_with_deficit_of_cost_internal {n d : ℕ} (hd : 0 < d) {m k : ℝ}
    (hm : 0 ≤ m) (hk : 0 ≤ k)
    (hcost : m ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * (32768 * (194 : ℝ) ^ d)))
    (hkcost : k ≤ (n : ℝ) ^ ((d : ℝ)⁻¹) / (128 * (32768 * (194 : ℝ) ^ d))) :
    64 * (32768 * (194 : ℝ) ^ d * (m + k)) ^ d ≤ (n : ℝ) := by
  let C : ℝ := 32768 * (194 : ℝ) ^ d
  let r : ℝ := (n : ℝ) ^ ((d : ℝ)⁻¹)
  have hC : 0 < C := by dsimp [C]; positivity
  have hm' : m * (128 * C) ≤ r := (le_div_iff₀ (by positivity)).mp hcost
  have hk' : k * (128 * C) ≤ r := (le_div_iff₀ (by positivity)).mp hkcost
  have hstep : C * (m + k) ≤ r / 64 := by nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ C * (m + k) by positivity) hstep d
  have hrootpow : r ^ d = (n : ℝ) :=
    Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hd)
  rw [div_pow, hrootpow] at hpow
  have hden : (64 : ℝ) ≤ (64 : ℝ) ^ d := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 64) (Nat.succ_le_of_lt hd)
  have hh : 64 * ((n : ℝ) / (64 : ℝ) ^ d) ≤ n := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity) (sub_nonneg.mpr hden)]
  exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans hh

end Complexity.KarchmerWigderson
