/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionProbability
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: restriction tails

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionTails.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V] [DecidableEq V]

theorem restrictionAvg_pow_card_live (p a : ℝ) :
    restrictionAvg p (fun σ : Restriction V => a ^ Fintype.card (Live σ)) =
      (1 - p + p * a) ^ Fintype.card V := by
  rw [restrictionAvg_mask_sampler]
  calc
    _ = ∑ T : Finset V, (p * a) ^ T.card *
        (1 - p) ^ (Fintype.card V - T.card) := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [card_live_maskRestriction, finiteAvg_const, bernoulliWeight, mul_pow]
      ring
    _ = (p * a + (1 - p)) ^ Fintype.card V := by
      simpa only [Finset.prod_const, Finset.card_compl, Finset.card_univ] using
        (Fintype.prod_add (fun _ : V => p * a) (fun _ : V => 1 - p)).symm
    _ = _ := by congr 1 ; ring

theorem restrictionAvg_two_pow_live (p : ℝ) :
    restrictionAvg p (fun σ : Restriction V =>
      (2 : ℝ) ^ (Fintype.card (Live σ) : ℝ)) = (1 + p) ^ Fintype.card V := by
  calc
    _ = (1 - p + p * 2) ^ Fintype.card V := by
      simpa only [Real.rpow_natCast] using restrictionAvg_pow_card_live (V := V) p 2
    _ = _ := by congr 1 ; ring

theorem restrictionAvg_two_neg_pow_live (p : ℝ) :
    restrictionAvg p (fun σ : Restriction V =>
      (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ))) = (1 - p / 2) ^ Fintype.card V := by
  simp_rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, ← inv_pow]
  rw [restrictionAvg_pow_card_live]
  congr 1 ; ring

theorem one_add_pow_le_exp (p : ℝ) (hp : 0 ≤ p) (n : ℕ) :
    (1 + p) ^ n ≤ Real.exp (p * n) := by
  calc
    _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp p]) n
    _ = Real.exp (p * n) := by rw [← Real.exp_nat_mul]; congr 1 ; ring

theorem one_sub_half_pow_le_exp (p : ℝ) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p / 2) ^ n ≤ Real.exp (-(p * n) / 2) := by
  calc
    _ ≤ (Real.exp (-(p / 2))) ^ n := pow_le_pow_left₀ (by linarith)
      (Real.one_sub_le_exp_neg (p / 2)) n
    _ = Real.exp (-(p * n) / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1 ; ring

private theorem lower_tail_exponent (μ : ℝ) (hμ : 0 ≤ μ) :
    (2 : ℝ) ^ (μ / 2) * Real.exp (-μ / 2) ≤ (2 : ℝ) ^ (-μ / 16) := by
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ (3 / 4 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlog hμ
  nlinarith

private theorem upper_tail_exponent (μ : ℝ) (hμ : 0 ≤ μ) :
    (2 : ℝ) ^ (-(2 * μ)) * Real.exp μ ≤ (2 : ℝ) ^ (-μ / 16) := by
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlog hμ
  nlinarith

theorem restrictionAvg_lower_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    restrictionAvg p (fun σ : Restriction V =>
      if (Fintype.card (Live σ) : ℝ) < (p * Fintype.card V) / 2 then 1 else 0) ≤
      (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  let μ : ℝ := p * Fintype.card V
  have hμ : 0 ≤ μ := mul_nonneg hp (Nat.cast_nonneg _)
  have hmajor : ∀ σ : Restriction V,
      (if (Fintype.card (Live σ) : ℝ) < μ / 2 then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (μ / 2) * (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ)) := by
    intro σ
    by_cases hσ : (Fintype.card (Live σ) : ℝ) < μ / 2
    · rw [ite_eq_left hσ, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact Real.one_le_rpow (by norm_num) (by linarith)
    · rw [ite_eq_right hσ]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ restrictionAvg p (fun σ : Restriction V =>
        (2 : ℝ) ^ (μ / 2) * (2 : ℝ) ^ (-(Fintype.card (Live σ) : ℝ))) :=
      restrictionAvg_mono hp hp1 hmajor
    _ = (2 : ℝ) ^ (μ / 2) * (1 - p / 2) ^ Fintype.card V := by
      rw [restrictionAvg_const_mul, restrictionAvg_two_neg_pow_live]
    _ ≤ (2 : ℝ) ^ (μ / 2) * Real.exp (-μ / 2) :=
      mul_le_mul_of_nonneg_left (one_sub_half_pow_le_exp p hp1 _)
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := lower_tail_exponent μ hμ

theorem restrictionAvg_upper_tail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    restrictionAvg p (fun σ : Restriction V =>
      if 2 * (p * Fintype.card V) < (Fintype.card (Live σ) : ℝ) then 1 else 0) ≤
      (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  let μ : ℝ := p * Fintype.card V
  have hμ : 0 ≤ μ := mul_nonneg hp (Nat.cast_nonneg _)
  have hmajor : ∀ σ : Restriction V,
      (if 2 * μ < (Fintype.card (Live σ) : ℝ) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-(2 * μ)) * (2 : ℝ) ^ (Fintype.card (Live σ) : ℝ) := by
    intro σ
    by_cases hσ : 2 * μ < (Fintype.card (Live σ) : ℝ)
    · rw [ite_eq_left hσ, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact Real.one_le_rpow (by norm_num) (by linarith)
    · rw [ite_eq_right hσ]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by norm_num) _)
  calc
    _ ≤ restrictionAvg p (fun σ : Restriction V =>
        (2 : ℝ) ^ (-(2 * μ)) * (2 : ℝ) ^ (Fintype.card (Live σ) : ℝ)) :=
      restrictionAvg_mono hp hp1 hmajor
    _ = (2 : ℝ) ^ (-(2 * μ)) * (1 + p) ^ Fintype.card V := by
      rw [restrictionAvg_const_mul, restrictionAvg_two_pow_live]
    _ ≤ (2 : ℝ) ^ (-(2 * μ)) * Real.exp μ :=
      mul_le_mul_of_nonneg_left (one_add_pow_le_exp p hp _)
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := upper_tail_exponent μ hμ

theorem restrictionAvg_outside_window (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    restrictionAvg p (fun σ : Restriction V =>
      if ¬((p * Fintype.card V) / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
        (Fintype.card (Live σ) : ℝ) ≤ 2 * (p * Fintype.card V)) then 1 else 0) ≤
      2 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  let μ : ℝ := p * Fintype.card V
  have hsplit : ∀ σ : Restriction V,
      (if ¬(μ / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
        (Fintype.card (Live σ) : ℝ) ≤ 2 * μ) then (1 : ℝ) else 0) ≤
      (if (Fintype.card (Live σ) : ℝ) < μ / 2 then (1 : ℝ) else 0) +
        (if 2 * μ < (Fintype.card (Live σ) : ℝ) then (1 : ℝ) else 0) := by
    intro σ
    by_cases hlo : (Fintype.card (Live σ) : ℝ) < μ / 2
    · by_cases hhi : 2 * μ < (Fintype.card (Live σ) : ℝ) <;>
        simp [hlo, hhi, not_le.mpr hlo]
    · have hlo' := le_of_not_gt hlo
      by_cases hhi : 2 * μ < (Fintype.card (Live σ) : ℝ)
      · simp [hlo, hhi, not_le.mpr hhi]
      · simp [hlo, hhi, hlo', le_of_not_gt hhi]
  calc
    _ ≤ restrictionAvg p (fun σ : Restriction V =>
        (if (Fintype.card (Live σ) : ℝ) < μ / 2 then (1 : ℝ) else 0) +
          (if 2 * μ < (Fintype.card (Live σ) : ℝ) then (1 : ℝ) else 0)) :=
      restrictionAvg_mono hp hp1 hsplit
    _ = restrictionAvg p (fun σ : Restriction V =>
          if (Fintype.card (Live σ) : ℝ) < μ / 2 then 1 else 0) +
        restrictionAvg p (fun σ : Restriction V =>
          if 2 * μ < (Fintype.card (Live σ) : ℝ) then 1 else 0) :=
      restrictionAvg_add p _ _
    _ ≤ (2 : ℝ) ^ (-μ / 16) + (2 : ℝ) ^ (-μ / 16) :=
      add_le_add (restrictionAvg_lower_tail p hp hp1) (restrictionAvg_upper_tail p hp hp1)
    _ = _ := by ring

end DepthThreeLowerBound

end

end Complexity
