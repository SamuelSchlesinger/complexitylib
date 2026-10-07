/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageParameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: language parameter bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageParameterBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

namespace DepthThreeLowerBound

private theorem rpow_two_thirds_cube (d : ℕ) :
    ((d : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (d : ℝ) ^ 2 := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d) (2 / 3 : ℝ) 3]
  norm_num

private theorem rpow_one_sixth_sixth (d : ℕ) :
    ((d : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = (d : ℝ) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg d) (1 / 6 : ℝ) 6]
  norm_num

theorem hashDimension_rpow_lower (d : ℕ) :
    (d : ℝ) ^ (2 / 3 : ℝ) ≤ (hashDimension d : ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0)
    (Nat.cast_nonneg (hashDimension d))
  rw [rpow_two_thirds_cube]
  exact_mod_cast hashDimension_cube_bound d

theorem hashDimension_rpow_lt_add_one (d : ℕ) (hd : 0 < d) :
    (hashDimension d : ℝ) < (d : ℝ) ^ (2 / 3 : ℝ) + 1 := by
  have hr := hashDimension_pos hd
  by_cases hrone : hashDimension d = 1
  · have hpos := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hd) (2 / 3 : ℝ)
    rw [hrone]
    norm_num only [Nat.cast_one]
    linarith
  · have hpredpos : 0 < hashDimension d - 1 := by omega
    have hpred : (hashDimension d - 1) ^ 3 < d ^ 2 := by
      by_contra h
      have hle := hashDimension_minimal hd hpredpos (Nat.le_of_not_gt h)
      omega
    have hpredreal : ((hashDimension d - 1 : ℕ) : ℝ) <
        (d : ℝ) ^ (2 / 3 : ℝ) := by
      apply lt_of_pow_lt_pow_left₀ 3 (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      rw [rpow_two_thirds_cube]
      exact_mod_cast hpred
    have hcast : ((hashDimension d - 1 : ℕ) : ℝ) =
        (hashDimension d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ hashDimension d)] ; norm_num
    rw [hcast] at hpredreal
    linarith

theorem hashDimension_rpow_upper (d : ℕ) (hd : 1 ≤ d) :
    (hashDimension d : ℝ) ≤ 2 * (d : ℝ) ^ (2 / 3 : ℝ) := by
  have hround := hashDimension_rpow_lt_add_one d (by omega)
  have hone : (1 : ℝ) ≤ (d : ℝ) ^ (2 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
  linarith

theorem independenceOrder_rpow_le (d : ℕ) :
    (independenceOrder d : ℝ) ≤ (d : ℝ) ^ (1 / 6 : ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : (6 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  rw [rpow_one_sixth_sixth]
  exact_mod_cast independenceOrder_pow_le d

theorem rpow_lt_independenceOrder_add_two (d : ℕ) :
    (d : ℝ) ^ (1 / 6 : ℝ) < (independenceOrder d : ℝ) + 2 := by
  apply lt_of_pow_lt_pow_left₀ 6
    (by linarith [(Nat.cast_nonneg (independenceOrder d) :
      (0 : ℝ) ≤ (independenceOrder d : ℝ))] :
      (0 : ℝ) ≤ (independenceOrder d : ℝ) + 2)
  rw [rpow_one_sixth_sixth]
  exact_mod_cast independenceOrder_next_pow_gt d

theorem four_le_rpow_one_sixth (d : ℕ) (hd : 4096 ≤ d) :
    (4 : ℝ) ≤ (d : ℝ) ^ (1 / 6 : ℝ) := by
  apply le_of_pow_le_pow_left₀ (by decide : (6 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  rw [rpow_one_sixth_sixth]
  norm_num only [show (4 : ℝ) ^ 6 = 4096 by norm_num]
  exact_mod_cast hd

theorem half_rpow_le_independenceOrder (d : ℕ) (hd : 4096 ≤ d) :
    (d : ℝ) ^ (1 / 6 : ℝ) / 2 ≤ (independenceOrder d : ℝ) := by
  have hfour := four_le_rpow_one_sixth d hd
  have hnext := rpow_lt_independenceOrder_add_two d
  linarith

theorem independenceOrder_add_two_mul_hashDimension_le (d : ℕ) (hd : 4096 ≤ d) :
    (independenceOrder d + 2) * hashDimension d ≤ 3 * d := by
  have hdreal : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdreal
  have ht := independenceOrder_rpow_le d
  have hr := hashDimension_rpow_upper d (by omega)
  have hfour := four_le_rpow_one_sixth d hd
  have hy : 0 ≤ (d : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hproduct : ((independenceOrder d : ℝ) + 2) * (hashDimension d : ℝ) ≤
      ((d : ℝ) ^ (1 / 6 : ℝ) + 2) * (2 * (d : ℝ) ^ (2 / 3 : ℝ)) :=
    mul_le_mul (by linarith) hr
      (Nat.cast_nonneg (hashDimension d)) (by linarith)
  have hslack : 0 ≤ ((d : ℝ) ^ (1 / 6 : ℝ) - 4) *
      ((d : ℝ) ^ (2 / 3 : ℝ)) :=
    mul_nonneg (by linarith) hy
  have hsum : (d : ℝ) ^ (1 / 6 : ℝ) * (d : ℝ) ^ (2 / 3 : ℝ) =
      (d : ℝ) ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add hdpos]
    norm_num
  have hlast : (d : ℝ) ^ (5 / 6 : ℝ) ≤ (d : ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hdreal (by norm_num : (5 / 6 : ℝ) ≤ 1))
  have hreal : ((independenceOrder d : ℝ) + 2) * (hashDimension d : ℝ) ≤
      3 * (d : ℝ) := by
    nlinarith [hproduct, hslack, hsum, hlast]
  exact_mod_cast hreal

theorem blockLen_le_five_mul (d : ℕ) (hd : 4096 ≤ d) :
    blockLen d ≤ 5 * d := by
  have hprod := independenceOrder_add_two_mul_hashDimension_le d hd
  rw [blockLen_eq (by omega : 0 < d)]
  omega

theorem blockLen_dataDimension_le (n : ℕ) (hn : 20480 ≤ n) :
    blockLen (dataDimension n) ≤ n := by
  have hd : 4096 ≤ dataDimension n := by
    unfold dataDimension
    omega
  exact (blockLen_le_five_mul (dataDimension n) hd).trans (five_mul_dataDimension_le n)

end DepthThreeLowerBound

end

end Complexity
