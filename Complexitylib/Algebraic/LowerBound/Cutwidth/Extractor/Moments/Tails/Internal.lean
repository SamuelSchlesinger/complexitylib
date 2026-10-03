/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
public import Mathlib.Analysis.Real.Sqrt
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.FourthMoment
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normalizing the first four sign-sum moments

The raw parity-bias bounds, divided by powers of the square root of the number
of signs, satisfy the approximate-moment certificate in `FourthMoment`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem mean_div_pow {α : Type*} (s : Finset α) (w X : α → ℝ)
    (r : ℝ) (k : Nat) :
    (∑ a ∈ s, w a * (X a / r) ^ k) =
      weightedMean s w (fun a => X a ^ k) / r ^ k := by
  simp only [div_pow]
  simp only [div_eq_mul_inv, weightedMean, Finset.sum_mul, mul_assoc]

theorem signSum_tails_of_parityBias {α : Type*} {m : Nat} {s : Finset α}
    {w : α → ℝ} {σ : α → Fin m → ℝ} {δ : ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (hδ : 0 ≤ δ) (hbudget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (h : ParityBiasBound s w σ δ) :
    ((1 / 36 : ℝ) ≤ ∑ a ∈ s, if Real.sqrt (m : ℝ) / 8 < signSum σ a then w a else 0) ∧
      ((1 / 36 : ℝ) ≤ ∑ a ∈ s,
        if signSum σ a < -(Real.sqrt (m : ℝ) / 8) then w a else 0) := by
  let r := Real.sqrt (m : ℝ)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_iff.mpr hm
  have hr1 : 1 ≤ r := by simpa [r] using Real.sqrt_le_sqrt hm1
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hr2 : r ^ 2 = m := Real.sq_sqrt hm0.le
  have hr3 : r ^ 3 = (m : ℝ) * r := by
    calc
      r ^ 3 = r ^ 2 * r := by ring
      _ = (m : ℝ) * r := by rw [hr2]
  have hr4 : r ^ 4 = (m : ℝ) ^ 2 := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (m : ℝ) ^ 2 := by rw [hr2]
  have hb : (m : ℝ) ^ 2 * δ ≤ 1 / 100 := by nlinarith [hbudget]
  have h1 := signSum_first_moment h
  have h2 := signSum_second_moment hδ hmass hσ h
  have h3 := signSum_third_moment hσ h
  have h4 := signSum_fourth_moment hδ hmass hσ h
  have hmean : |∑ a ∈ s, w a * (signSum σ a / r)| ≤ 1 / 100 := by
    have heq : (∑ a ∈ s, w a * (signSum σ a / r)) =
        weightedMean s w (signSum σ) / r := by
      simpa only [pow_one] using mean_div_pow s w (signSum σ) r 1
    rw [heq, abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    have hmle : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hb1 := mul_le_mul_of_nonneg_right hmle hδ
    linarith
  have hsecond : (99 / 100 : ℝ) ≤ ∑ a ∈ s, w a * (signSum σ a / r) ^ 2 := by
    rw [mean_div_pow, hr2, le_div_iff₀ hm0]
    have hlow := (abs_le.mp h2).1
    linarith
  have hthird : |∑ a ∈ s, w a * (signSum σ a / r) ^ 3| ≤ 1 / 100 := by
    rw [mean_div_pow, abs_div, abs_of_pos (pow_pos hr0 _), div_le_iff₀ (pow_pos hr0 _)]
    have hb3 : (m : ℝ) ^ 3 * δ ≤ (m : ℝ) / 100 := by
      nlinarith [mul_le_mul_of_nonneg_left hb hm0.le]
    have hmle : (m : ℝ) ≤ r ^ 3 := by
      rw [hr3]
      exact le_mul_of_one_le_right hm0.le hr1
    linarith
  have hfourth : (∑ a ∈ s, w a * (signSum σ a / r) ^ 4) ≤ 301 / 100 := by
    rw [mean_div_pow, div_le_iff₀ (pow_pos hr0 _), hr4]
    have hb4 : (m : ℝ) ^ 4 * δ ≤ (m : ℝ) ^ 2 / 100 := by
      nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (m : ℝ))]
    linarith
  have hpos := fourthMoment_positive_tail_of_approx s w (fun a => signSum σ a / r)
    hw hmass hmean hsecond hthird hfourth
  have hneg := fourthMoment_negative_tail_of_approx s w (fun a => signSum σ a / r)
    hw hmass hmean hsecond hthird hfourth
  have hpos_iff (a : α) : (1 / 8 : ℝ) < signSum σ a / r ↔ r / 8 < signSum σ a := by
    rw [lt_div_iff₀ hr0]
    ring_nf
  have hneg_iff (a : α) : signSum σ a / r < -(1 / 8 : ℝ) ↔ signSum σ a < -(r / 8) := by
    rw [div_lt_iff₀ hr0]
    ring_nf
  constructor
  · simpa only [hpos_iff] using hpos
  · simpa only [hneg_iff] using hneg

end Algebraic.Cutwidth.Extractor.Internal
