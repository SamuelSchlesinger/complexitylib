/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Demand
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # Exponential error below the frontier size threshold -/

@[expose] public section

namespace Complexity.Frontier

open Filter Asymptotics

/-- Below `(1 + 1/A - ε)n`, frontier counts have an exponential margin. The independent
condition `γ < 1` also absorbs the small output classes when many inputs are unused. -/
theorem eventually_frontier_log_error {A ε γ : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hγ1 : γ < 1) (hγε : γ < A * ε) (K : ℕ → ℕ)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)) :
    ∃ η > 0, ∀ C : ℝ, ∀ᶠ n : ℕ in atTop,
      1 + 2 * Real.logb 2 (K n) ≤ (1 - γ) * n ∧
      ∀ s v w : ℝ, 0 ≤ s → 0 ≤ v → s ≤ (1 + 1 / A - ε) * n → v ≤ 4 * s + 3 →
        w ≤ (A + η) * (s - n + Real.logb 2 (K n) + 1) + η * v + C →
        w + 4 + 3 * Real.logb 2 (K n) + Real.logb 2 (v + 1) ≤ (1 - γ) * n := by
  let L := 1 + 1 / A
  let B := 1 / A + 4 * L
  let δ := A * ε - γ
  let η := δ / (2 * (B + 1))
  have hL : 0 < L := by dsimp [L]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hηB : η * B ≤ δ / 2 := by
    have hηeq : η * (2 * (B + 1)) = δ := by dsimp [η]; field_simp
    nlinarith
  have hlogK : (fun n => Real.logb 2 (K n)) =o[atTop] fun n => (n : ℝ) := by
    simpa only [Real.logb, div_eq_mul_inv, one_mul, mul_comm] using
      hK.const_mul_left (1 / Real.log 2)
  have hconst (c : ℝ) : (fun _ : ℕ => c) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_const_left.mpr (Or.inr
      (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
  have hsmall := (hconst 1).add (hlogK.const_mul_left 2)
  refine ⟨η, hη, fun C => ?_⟩
  have hlogV : (fun n : ℕ => Real.logb 2 (4 * L * n + 4)) =o[atTop] fun n => (n : ℝ) := by
    have H := (isLittleO_log_affine (α := 4 * L) (β := 4) (by positivity)
      (by norm_num)).const_mul_left (1 / Real.log 2)
    simpa only [Real.logb, div_eq_mul_inv, one_mul, mul_comm] using H
  let e := fun n : ℕ => (A + η + 3) * Real.logb 2 (K n) +
    Real.logb 2 (4 * L * n + 4) + (A + 4 * η + C + 4)
  have he : e =o[atTop] fun n => (n : ℝ) :=
    ((hlogK.const_mul_left _).add hlogV).add (hconst _)
  filter_upwards [hsmall.bound (show 0 < 1 - γ by linarith),
    he.bound (show 0 < δ / 2 by positivity)] with n hsmalln hen
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hn] at hsmalln hen
  refine ⟨(le_abs_self _).trans hsmalln, ?_⟩
  intro s v w hs hv hsize hvsize hw
  have hsL : s ≤ L * n := by dsimp [L]; nlinarith
  have hvL : v + 1 ≤ 4 * L * n + 4 := by nlinarith
  have hlogv : Real.logb 2 (v + 1) ≤ Real.logb 2 (4 * L * n + 4) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hvL
  have hsupply : (A + η) * (s - n) ≤ (1 - A * ε + η / A) * n := by
    have H := mul_le_mul_of_nonneg_left
      (show s - n ≤ (1 / A - ε) * n by linarith) (by positivity : 0 ≤ A + η)
    have heq : (A + η) * ((1 / A - ε) * n) =
        (1 - A * ε + η / A) * n - η * ε * n := by field_simp; ring
    rw [heq] at H
    nlinarith [mul_nonneg (mul_nonneg hη.le hε.le) hn]
  have hηv : η * v ≤ 4 * η * L * n + 3 * η := by nlinarith
  have hηBn := mul_le_mul_of_nonneg_right hηB hn
  have hηBn' : (η / A + 4 * η * L) * n ≤ δ / 2 * n := by
    have heq : η * B * n = (η / A + 4 * η * L) * n := by dsimp [B]; ring
    rwa [heq] at hηBn
  have he' : e n ≤ δ / 2 * n := (le_abs_self _).trans hen
  dsimp [e, δ] at he' hηBn'
  nlinarith

/-- A logarithmic count bound becomes an exponentially small fraction of all Boolean inputs. -/
theorem div_two_pow_le_of_logb {x γ : ℝ} {n : ℕ} (hx : 0 < x)
    (h : Real.logb 2 x ≤ (1 - γ) * n) :
    x / (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (-γ * n) := by
  have H := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx).mp h
  calc x / (2 : ℝ) ^ n ≤ (2 : ℝ) ^ ((1 - γ) * n) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_right H (by positivity)
    _ = (2 : ℝ) ^ (-γ * n) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end Complexity.Frontier
