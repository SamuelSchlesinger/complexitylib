/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Parameters

/-!
# Constants for shared-control restrictions and wide conjunction messages

The affine saving at intersecting exact-two gates combines with the stronger
one-eighth bias of wide conjunctions. Its coefficient strictly exceeds the
previous joint-graph coefficient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Shared

/-- Entropy in bits of a conjunction of three independent unbiased literals. -/
noncomputable def wideEntropy : ℝ := Real.binEntropy (1 / 8) / Real.log 2

/-- Information saved by a conjunction involving at least three primary variables. -/
noncomputable def wideSaving : ℝ := 1 - wideEntropy

/-- The whole-basis coefficient obtained from shared primary controls. -/
noncomputable def gateCoefficient : ℝ :=
  (1 - Joint.overlapPenalty + Joint.gateSaving / 2 + 3 * wideSaving / 2) / (1 + wideSaving)

/-- Fraction of designated triples retained after a logarithmic receiving side. -/
noncomputable def receiverRetention (n k : ℕ) : ℝ :=
  ((n : ℝ) - k - 1) * (n - k - 2) * (n - k - 3) / (n * (n - 1) * (n - 2))

/-- A sending side with at least three coordinates has nonnegative triple retention. -/
theorem receiverRetention_nonneg {n k : ℕ} (range : k + 4 ≤ n) :
    0 ≤ receiverRetention n k := by
  have rangeR : (k : ℝ) + 4 ≤ n := by exact_mod_cast range
  have kR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  unfold receiverRetention
  apply div_nonneg
  · apply mul_nonneg
    · apply mul_nonneg <;> linarith
    · linarith
  · apply mul_nonneg
    · apply mul_nonneg <;> linarith
    · linarith

/-- The one-eighth entropy has an exact expression using the logarithm of seven. -/
theorem wideEntropy_eq : wideEntropy = 3 - (7 / 8) * (Real.log 7 / Real.log 2) := by
  have log8 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have entropy : Real.binEntropy (1 / 8) = 3 * Real.log 2 - (7 / 8) * Real.log 7 := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num [Real.negMulLog_def, Real.log_div, log8]
    ring
  rw [wideEntropy, entropy]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

/-- A wide conjunction saves a positive number of bits. -/
theorem wideSaving_pos : 0 < wideSaving := by
  have less : wideEntropy < 1 := by
    rw [wideEntropy, div_lt_one (Real.log_pos (by norm_num))]
    exact Real.binEntropy_lt_log_two.mpr (by norm_num)
  unfold wideSaving
  linarith

/-- The one-eighth bias saves strictly more than the joint two-variable gate charge. -/
theorem gateSaving_lt_wideSaving : Joint.gateSaving < wideSaving := by
  have compare : Real.log ((2 : ℝ) ^ 28) < Real.log ((7 : ℝ) ^ 7 * (3 : ℝ) ^ 6) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at compare
  norm_num only [Nat.cast_ofNat] at compare
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have scaled := (div_lt_div_iff_of_pos_right hlog).mpr compare
  rw [wideSaving, wideEntropy_eq, Joint.gateSaving, Joint.quarterEntropy_eq]
  field_simp at scaled ⊢
  linarith

/-- Twice the two-variable gate saving dominates the one-eighth saving. -/
theorem wideSaving_lt_two_mul_gateSaving : wideSaving < 2 * Joint.gateSaving := by
  have compare : Real.log ((3 : ℝ) ^ 12 * (7 : ℝ) ^ 7) < Real.log ((2 : ℝ) ^ 40) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at compare
  norm_num only [Nat.cast_ofNat] at compare
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have scaled := (div_lt_div_iff_of_pos_right hlog).mpr compare
  rw [wideSaving, wideEntropy_eq, Joint.gateSaving, Joint.quarterEntropy_eq]
  field_simp at scaled ⊢
  linarith

/-- Shared-control preprocessing strictly improves the preceding joint coefficient. -/
theorem old_gateCoefficient_lt : Joint.gateCoefficient < gateCoefficient := by
  have rho := Joint.gateSaving_pos
  have r := wideSaving_pos
  have gap := gateSaving_lt_wideSaving
  have relation : Joint.overlapPenalty = Joint.gateSaving - 1 / 4 := by
    unfold Joint.overlapPenalty Joint.gateSaving
    ring
  rw [Joint.gateCoefficient_eq, gateCoefficient,
    div_lt_div_iff₀ (by linarith : 0 < 1 + Joint.gateSaving)
      (by linarith : 0 < 1 + wideSaving)]
  rw [relation]
  nlinarith [mul_pos (sub_pos.mpr gap)
    (by linarith : 0 < 1 / 4 + Joint.gateSaving / 2)]

/-- The resulting gate coefficient is strictly above one. -/
theorem one_lt_gateCoefficient : 1 < gateCoefficient :=
  lt_trans Joint.one_lt_gateCoefficient old_gateCoefficient_lt

end Algebraic.Cutwidth.Aggregate.Geometry.Shared
