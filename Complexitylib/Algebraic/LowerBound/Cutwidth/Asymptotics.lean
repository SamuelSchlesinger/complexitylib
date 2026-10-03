/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Foundations.Data.Nat.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Logarithmic remainders in the cutwidth argument

Fixed logarithmic terms, including the integral ceiling logarithm in the
finite graph bounds, can be absorbed in every positive linear slack.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open Filter

/-- Every fixed multiple of the binary logarithm, plus a constant, is
eventually below every positive multiple of the input. -/
theorem eventually_mul_logb_add_lt (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : Nat in atTop, A * Real.logb 2 n + B < δ * n := by
  have hlog : (fun n : Nat => Real.log n) =o[atTop] (fun n : Nat => (n : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * |A| / (δ * Real.log 2))
  have key := (Asymptotics.isLittleO_iff_nat_mul_le.mp hlog) m
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * B / δ)
  filter_upwards [key, eventually_ge_atTop 1, eventually_ge_atTop N] with n hn hn1 hnN
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1'
  rw [Real.norm_of_nonneg hlogn, Real.norm_of_nonneg (by positivity)] at hn
  have hmA : 2 * |A| < m * (δ * Real.log 2) := by
    rwa [div_lt_iff₀ (by positivity)] at hm
  have h₁ : 2 * (A * Real.logb 2 n) ≤ δ * n := by
    rw [Real.logb]
    have step : 2 * A * Real.log n ≤ (m * (δ * Real.log 2)) * Real.log n := by
      apply mul_le_mul_of_nonneg_right _ hlogn
      have := le_abs_self A
      linarith
    have step' : (m * (δ * Real.log 2)) * Real.log n ≤ δ * Real.log 2 * n := by
      have : (m : ℝ) * Real.log n ≤ n := hn
      calc (m * (δ * Real.log 2)) * Real.log n = δ * Real.log 2 * (m * Real.log n) := by ring
        _ ≤ δ * Real.log 2 * n := mul_le_mul_of_nonneg_left this (by positivity)
    have : 2 * A * Real.log n ≤ δ * Real.log 2 * n := step.trans step'
    calc 2 * (A * (Real.log n / Real.log 2)) = (2 * A * Real.log n) / Real.log 2 := by ring
      _ ≤ (δ * Real.log 2 * n) / Real.log 2 := by gcongr
      _ = δ * n := by field_simp
  have h₂ : 2 * B < δ * n := by
    have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  linarith

/-- The ceiling binary logarithm plus a constant is eventually smaller
than every positive linear function. -/
theorem eventually_clog_add_lt (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : Nat in atTop, (Nat.clog 2 n : ℝ) + B < δ * n := by
  filter_upwards [eventually_mul_logb_add_lt 1 (B + 1) hδ, eventually_ge_atTop 1]
    with n hn hn1
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast hn1)
  have hclog : (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
    rw [← Real.natCeil_logb_natCast 2 n]
    exact Nat.ceil_lt_add_one hlog
  linarith

end Algebraic.Cutwidth
