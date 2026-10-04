/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Parameters

/-!
# Constants for joint conjunction messages

Revealing a graph of two-variable conjunctions charges a seed edge its binary
entropy, a further tree edge three quarters of a bit, and every remaining edge
three halves of a bit minus the seed entropy. The resulting joint information
bound improves the coefficient from the separate-coordinate entropy argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

/-- Entropy in bits of a conjunction of two independent unbiased literals. -/
noncomputable def quarterEntropy : ℝ := Real.binEntropy (1 / 4) / Real.log 2

/-- The variable charge in the joint conjunction-message bound. -/
noncomputable def overlapPenalty : ℝ := quarterEntropy - 3 / 4

/-- The gate saving after accounting for shared primary variables. -/
noncomputable def gateSaving : ℝ := quarterEntropy - 1 / 2

/-- The coefficient supplied by joint message counting and affine restrictions. -/
noncomputable def gateCoefficient : ℝ := (quarterEntropy + 3 / 4) / (quarterEntropy + 1 / 2)

/-- An exact logarithmic expression for the two-literal entropy. -/
theorem quarterEntropy_eq : quarterEntropy = 2 - (3 / 4) * (Real.log 3 / Real.log 2) := by
  have log4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have entropy : Real.binEntropy (1 / 4) = 2 * Real.log 2 - (3 / 4) * Real.log 3 := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    norm_num [Real.negMulLog_def, Real.log_div, log4]
    ring
  rw [quarterEntropy, entropy]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

/-- The seed entropy exceeds three quarters of a bit, since `27 < 32`. -/
theorem three_quarters_lt_quarterEntropy : (3 / 4 : ℝ) < quarterEntropy := by
  have compare : Real.log ((3 : ℝ) ^ 3) < Real.log ((2 : ℝ) ^ 5) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at compare
  norm_num only [Nat.cast_ofNat] at compare
  rw [quarterEntropy_eq]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ratio : Real.log 3 / Real.log 2 < 5 / 3 := by
    apply (div_lt_iff₀ hlog).mpr
    linarith
  linarith

/-- A conjunction carries strictly less than one bit. -/
theorem quarterEntropy_lt_one : quarterEntropy < 1 := by
  rw [quarterEntropy, div_lt_one (Real.log_pos (by norm_num))]
  exact Real.binEntropy_lt_log_two.mpr (by norm_num)

/-- The graph variable charge is positive. -/
theorem overlapPenalty_pos : 0 < overlapPenalty := by
  unfold overlapPenalty
  linarith [three_quarters_lt_quarterEntropy]

/-- The graph variable charge is less than one quarter. -/
theorem overlapPenalty_lt_quarter : overlapPenalty < 1 / 4 := by
  unfold overlapPenalty
  linarith [quarterEntropy_lt_one]

/-- The joint gate saving is positive. -/
theorem gateSaving_pos : 0 < gateSaving := by
  unfold gateSaving
  linarith [three_quarters_lt_quarterEntropy]

/-- The coefficient in the form arising from the two finite inequalities. -/
theorem gateCoefficient_eq : gateCoefficient =
    (1 - overlapPenalty + 2 * gateSaving) / (1 + gateSaving) := by
  unfold gateCoefficient overlapPenalty gateSaving
  congr 1 <;> ring

/-- Joint counting strictly improves the previous separate-coordinate coefficient. -/
theorem old_gateCoefficient_lt : Geometry.gateCoefficient < gateCoefficient := by
  have hc : Entropy.bitSaving = 1 - quarterEntropy := Entropy.bitSaving_eq
  have hh : 0 < quarterEntropy := by linarith [three_quarters_lt_quarterEntropy]
  have hd₁ : 0 < 2 - quarterEntropy := by linarith [quarterEntropy_lt_one]
  have hd₂ : 0 < quarterEntropy + 1 / 2 := by linarith
  rw [Geometry.gateCoefficient, hc, gateCoefficient]
  have denom : 1 + (1 - quarterEntropy) = 2 - quarterEntropy := by ring
  rw [denom, div_lt_div_iff₀ hd₁ hd₂]
  have hp := overlapPenalty_pos
  unfold overlapPenalty at hp
  nlinarith [mul_pos hh hp]

/-- The joint coefficient is strictly above one. -/
theorem one_lt_gateCoefficient : 1 < gateCoefficient :=
  lt_trans Geometry.one_lt_gateCoefficient old_gateCoefficient_lt

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
