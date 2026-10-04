/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Parameters.Defs
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite union and majority budgets

Power identities are first proved at symbolic exponents. The final margin
bound uses the discarded-coordinate allowance `2^(3b+1)`, at most half the
outer coordinates and at most one eighth of the square root of their
retained count when `b >= 5`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem sourceReductionOuterCount_pos (b : Nat) : 0 < sourceReductionOuterCount b := by
  unfold sourceReductionOuterCount
  positivity

theorem sourceReductionCandidateCount_pos (b : Nat) : 0 < sourceReductionCandidateCount b := by
  unfold sourceReductionCandidateCount
  positivity

theorem sourceReductionTamperingCount_pos (b : Nat) : 0 < sourceReductionTamperingCount b := by
  have positive := sourceReductionCandidateCount_pos b
  unfold sourceReductionTamperingCount
  lia

theorem sourceReductionTamperingCount_add_one (b : Nat) :
    sourceReductionTamperingCount b + 1 = 4 * sourceReductionCandidateCount b := by
  have positive := sourceReductionCandidateCount_pos b
  unfold sourceReductionTamperingCount
  lia

theorem sourceReductionAdviceLength_pos {b : Nat} (positive : 0 < b) :
    0 < sourceReductionAdviceLength b := by
  unfold sourceReductionAdviceLength sourceReductionOuterBits
  lia

theorem sourceReductionSamplerError_pos (b : Nat) : 0 < sourceReductionSamplerError b := by
  unfold sourceReductionSamplerError
  positivity

theorem sourceReductionBadThreshold_pos (b : Nat) : 0 < sourceReductionBadThreshold b := by
  unfold sourceReductionBadThreshold
  positivity

theorem sourceReductionParityBias_nonneg (b : Nat) : 0 ≤ sourceReductionParityBias b := by
  unfold sourceReductionParityBias
  exact mul_nonneg (by norm_num) (sourceReductionBadThreshold_pos b).le

private theorem power_union_budget (a c d : Nat) :
    (2 : ℝ) ^ a * ((2 : ℝ) ^ (a + c + d))⁻¹ / ((2 : ℝ) ^ c)⁻¹ =
      ((2 : ℝ) ^ d)⁻¹ := by
  rw [pow_add, pow_add]
  field_simp

theorem sourceReduction_union_budget (b : Nat) :
    (sourceReductionOuterCount b : ℝ) ^ 4 * sourceReductionCandidateCount b *
      (((2 : ℝ) ^ sourceReductionTarget b)⁻¹ / sourceReductionBadThreshold b) =
        sourceReductionSamplerError b := by
  simp only [sourceReductionOuterCount, sourceReductionOuterBits,
    sourceReductionCandidateCount, sourceReductionTarget, sourceReductionBadThreshold,
    sourceReductionSamplerError, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, ← pow_add]
  have exponent : 54 * b + sourceReductionCandidateBits b + 10 =
      (8 * b * 4 + sourceReductionCandidateBits b) + (17 * b + 10) + 5 * b := by lia
  rw [exponent]
  simpa only [mul_div_assoc] using
    power_union_budget (8 * b * 4 + sourceReductionCandidateBits b) (17 * b + 10) (5 * b)

private theorem power_moment_budget (b : Nat) :
    100 * ((2 : ℝ) ^ (8 * b)) ^ 2 * (2 * ((2 : ℝ) ^ (17 * b + 10))⁻¹) ≤ 1 := by
  have denominator : 17 * b + 10 = 8 * b * 2 + b + 10 := by lia
  rw [denominator, pow_add, pow_add, ← pow_mul]
  have one : 1 ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
  field_simp
  nlinarith

theorem sourceReduction_moment_budget {b m : Nat} (size : m ≤ sourceReductionOuterCount b) :
    100 * (m : ℝ) ^ 2 * sourceReductionParityBias b ≤ 1 := by
  have castSize : (m : ℝ) ≤ sourceReductionOuterCount b := by exact_mod_cast size
  have square := pow_le_pow_left₀ (Nat.cast_nonneg m) castSize 2
  calc
    _ ≤ 100 * (sourceReductionOuterCount b : ℝ) ^ 2 * sourceReductionParityBias b :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left square (by norm_num))
        (sourceReductionParityBias_nonneg b)
    _ ≤ 1 := by
      simpa only [sourceReductionOuterCount, sourceReductionOuterBits,
        sourceReductionParityBias, sourceReductionBadThreshold, Nat.cast_pow, Nat.cast_ofNat]
        using power_moment_budget b

theorem sourceReduction_bad_count_bound (b : Nat) :
    2 * sourceReductionSamplerError b * sourceReductionOuterCount b =
      (2 : ℝ) ^ (3 * b + 1) := by
  simp only [sourceReductionSamplerError, sourceReductionOuterCount,
    sourceReductionOuterBits, Nat.cast_pow, Nat.cast_ofNat]
  have exponent : 8 * b = 5 * b + 3 * b := by lia
  rw [exponent, pow_add, pow_add]
  field_simp

private theorem majority_margin {N m B : ℝ} (positive : 0 < N) (nonneg : 0 ≤ m)
    (discarded : 0 ≤ N - m) (bad : N - m ≤ B)
    (half : 2 * B ≤ N) (square : 128 * B ^ 2 ≤ N) :
    0 < m ∧ N - m ≤ Real.sqrt m / 8 := by
  have lower : N / 2 ≤ m := by linarith
  have strict : 0 < m := lt_of_lt_of_le (half_pos positive) lower
  have squared : (8 * (N - m)) ^ 2 ≤ m := by
    have monotone := pow_le_pow_left₀
      (mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num) discarded)
      (mul_le_mul_of_nonneg_left bad (show (0 : ℝ) ≤ 8 by norm_num)) 2
    nlinarith
  have root := (Real.le_sqrt (mul_nonneg (by norm_num) discarded) nonneg).mpr squared
  exact ⟨strict, by linarith⟩

theorem sourceReduction_majority_guards {b m : Nat} (large : 5 ≤ b)
    (size : m ≤ sourceReductionOuterCount b)
    (bad : ((sourceReductionOuterCount b - m : Nat) : ℝ) ≤
      2 * sourceReductionSamplerError b * sourceReductionOuterCount b) :
    0 < m ∧ ((sourceReductionOuterCount b - m : Nat) : ℝ) ≤ Real.sqrt (m : ℝ) / 8 := by
  rw [sourceReduction_bad_count_bound, Nat.cast_sub size] at bad
  have half : 2 * (2 : ℝ) ^ (3 * b + 1) ≤ (2 : ℝ) ^ (8 * b) := by
    calc
      _ = (2 : ℝ) ^ (3 * b + 2) := by
        rw [show 3 * b + 2 = (3 * b + 1) + 1 by lia]
        exact (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by lia)
  have square : 128 * ((2 : ℝ) ^ (3 * b + 1)) ^ 2 ≤ (2 : ℝ) ^ (8 * b) := by
    calc
      _ = (2 : ℝ) ^ (6 * b + 9) := by
        rw [← pow_mul, show 6 * b + 9 = 7 + (3 * b + 1) * 2 by lia, pow_add]
        norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by lia)
  have castCount : (sourceReductionOuterCount b : ℝ) = (2 : ℝ) ^ (8 * b) := by
    simp only [sourceReductionOuterCount, sourceReductionOuterBits, Nat.cast_pow, Nat.cast_ofNat]
  have result := majority_margin (N := (sourceReductionOuterCount b : ℝ))
    (m := (m : ℝ)) (B := (2 : ℝ) ^ (3 * b + 1))
    (by exact_mod_cast sourceReductionOuterCount_pos b) (Nat.cast_nonneg m)
    (sub_nonneg.mpr (by exact_mod_cast size)) bad
    (by rwa [castCount]) (by rwa [castCount])
  refine ⟨by exact_mod_cast result.1, ?_⟩
  simpa only [Nat.cast_sub size] using result.2

end Algebraic.Cutwidth.Extractor.Internal
