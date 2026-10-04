/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Parameters

/-!
# Exact logarithmic comparisons for conjunction tables

The local entropy comparisons reduce to small integer inequalities, avoiding
floating-point estimates in the circuit coefficient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-- The natural-log entropy of a conjunction of two unbiased literals. -/
theorem binEntropy_quarter_eq :
    Real.binEntropy (1 / 4) = 2 * Real.log 2 - (3 / 4) * Real.log 3 := by
  have h := Joint.quarterEntropy_eq
  unfold Joint.quarterEntropy at h
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp at h
  linarith

/-- Three quarters of a bit is strictly below the two-literal seed cost. -/
theorem three_quarters_log_lt_binEntropy_quarter :
    (3 / 4) * Real.log 2 < Real.binEntropy (1 / 4) := by
  exact (lt_div_iff₀ (Real.log_pos (by norm_num))).mp
    Joint.three_quarters_lt_quarterEntropy

/-- A parallel edge's cost is at most the spanning-tree extension charge. -/
theorem parallel_le_extension :
    (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) ≤ (3 / 4) * Real.log 2 := by
  linarith [three_quarters_log_lt_binEntropy_quarter]

/-- The remaining-edge charge is at least half a bit. -/
theorem half_le_chord : (1 / 2) * Real.log 2 ≤
    (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  linarith [Real.binEntropy_le_log_two (p := (1 / 4 : ℝ))]

/-- The worst shared-variable extension costs at most three quarters of a bit. -/
theorem extension_log_bound :
    3 * Real.log 2 - (5 / 8) * Real.log 5 - Real.binEntropy (1 / 4) ≤
      (3 / 4) * Real.log 2 := by
  have h : Real.log ((2 : ℝ) ^ 2 * 3 ^ 6) ≤ Real.log ((5 : ℝ) ^ 5) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  rw [binEntropy_quarter_eq]
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The triangle's largest conditional entropy fits the remaining-edge charge. -/
theorem triangle_log_bound :
    (5 / 4) * Real.log 2 - (3 / 8) * Real.log 3 ≤
      (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h : Real.log ((2 : ℝ) ^ 14) ≤ Real.log ((3 : ℝ) ^ 9) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  rw [binEntropy_quarter_eq]
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The triangle table with five assignments in one parent fibre. -/
theorem triangle_first_log_bound : (5 / 8) * Real.log 5 - Real.log 2 ≤
    (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h : Real.log ((5 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 4 * 3 ^ 6) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  rw [binEntropy_quarter_eq]
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The triangle table splitting its five-point parent fibre into two and three. -/
theorem triangle_second_log_bound :
    (5 / 8) * Real.log 5 - (1 / 4) * Real.log 2 - (3 / 8) * Real.log 3 ≤
      (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h : Real.log ((5 : ℝ) ^ 5 * 2 ^ 2) ≤ Real.log ((3 : ℝ) ^ 9) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  rw [binEntropy_quarter_eq]
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The four-variable table with both shared literals agreeing. -/
theorem disjoint_first_log_bound : (3 / 2) * Real.log 3 - (7 / 4) * Real.log 2 ≤
    (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h := three_quarters_log_lt_binEntropy_quarter
  rw [binEntropy_quarter_eq] at h ⊢
  linarith

/-- The four-variable table with exactly one shared literal agreeing. -/
theorem disjoint_second_log_bound :
    (21 / 16) * Real.log 3 - (1 / 4) * Real.log 2 - (7 / 16) * Real.log 7 ≤
      (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h : Real.log ((3 : ℝ) ^ 9 * 2 ^ 4) ≤ Real.log ((7 : ℝ) ^ 7) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  rw [binEntropy_quarter_eq]
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The four-variable table with neither shared literal agreeing. -/
theorem disjoint_third_log_bound :
    (9 / 8) * Real.log 3 - (1 / 2) * Real.log 2 - (5 / 16) * Real.log 5 ≤
      (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h : Real.log ((3 : ℝ) ^ 6) ≤ Real.log ((5 : ℝ) ^ 5) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  rw [binEntropy_quarter_eq]
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- Three forced literals save enough to be charged as a remaining graph edge. -/
theorem binEntropy_eighth_le_chord : Real.binEntropy (1 / 8) ≤
    (3 / 2) * Real.log 2 - Real.binEntropy (1 / 4) := by
  have h : Real.log ((2 : ℝ) ^ 28) ≤ Real.log ((3 : ℝ) ^ 6 * 7 ^ 7) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow,
    Real.log_pow] at h
  have log8 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have he : Real.binEntropy (1 / 8) = 3 * Real.log 2 - (7 / 8) * Real.log 7 := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num [Real.negMulLog_def, Real.log_div, log8]
    ring
  rw [he, binEntropy_quarter_eq]
  norm_num only [Nat.cast_ofNat] at h
  linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
