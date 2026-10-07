/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.LabelingBounds

/-!
# Sensitivity separation: labeling estimate

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/LabelingEstimate.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- An explicit numerical union-bound estimate. -/

namespace Internal

theorem labeling_union_bound_numerator {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (2*M^2+1)^16 * M^20 ≤ 3^16 * r^104 := by
  have hk : 2*M^2+1 ≤ 3*M^2 := by nlinarith
  have hp : M^52 ≤ r^104 := by
    calc
      M^52 ≤ (r^2)^52 := Nat.pow_le_pow_left hMr 52
      _ = r^104 := by rw [← pow_mul]
  calc
    (2*M^2+1)^16 * M^20 ≤ (3*M^2)^16 * M^20 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hk 16)
    _ = 3^16 * M^52 := by rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
    _ ≤ 3^16 * r^104 := Nat.mul_le_mul_left _ hp

theorem labeling_union_bound_constant {M : ℕ} (hM : 3 ≤ M) :
    3^16 < M^20 := by
  calc
    3^16 ≤ M^16 := Nat.pow_le_pow_left hM 16
    _ < M^20 := Nat.pow_lt_pow_right (by omega) (by omega)

theorem labeling_power_bound {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (2*M^2+1)^16 < r^104 := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  apply Nat.lt_of_mul_lt_mul_right (a := M^20)
  calc
    (2*M^2+1)^16 * M^20 ≤ 3^16*r^104 := labeling_union_bound_numerator hM hMr
    _ < M^20*r^104 := Nat.mul_lt_mul_of_pos_right (labeling_union_bound_constant hM)
      (pow_pos hr 104)
    _ = r^104*M^20 := Nat.mul_comm _ _

theorem labeling_union_bound_real {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r^2) :
    (((2*M^2+1)^16 : ℕ) : ℝ) / (r : ℝ)^104 ≤ 3^16 / (M : ℝ)^20 ∧
      3^16 / (M : ℝ)^20 < 1 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hrp : (0 : ℝ) < r := by
    have hr : 0 < r := (Nat.pow_pos_iff.mp
      (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
    exact_mod_cast hr
  constructor
  · apply (div_le_div_iff₀ (pow_pos hrp 104) (pow_pos hMp 20)).mpr
    exact_mod_cast labeling_union_bound_numerator hM hMr
  · apply (div_lt_one (pow_pos hMp 20)).mpr
    exact_mod_cast labeling_union_bound_constant hM

theorem labeling_sqrt_expression {M : ℕ} (hM : 0 < M) :
    (3*(M : ℝ)^2)^16 / (Real.sqrt M)^104 = 3^16 / (M : ℝ)^20 := by
  have hp : (0 : ℝ) < M := by exact_mod_cast hM
  have hd : (Real.sqrt M)^104 = (M : ℝ)^52 := by
    rw [show 104 = 2*52 from rfl, pow_mul, Real.sq_sqrt hp.le]
  rw [hd, div_eq_div_iff (pow_ne_zero _ hp.ne') (pow_ne_zero _ hp.ne'),
    mul_pow, ← pow_mul, mul_assoc, ← pow_add]

theorem labeling_source_estimate {M : ℕ} (hM : 3 ≤ M) :
    (((2*M^2+1)^16 : ℕ) : ℝ) / (Nat.ceil (Real.sqrt M) : ℝ)^104 ≤
        (3*(M : ℝ)^2)^16 / (Real.sqrt M)^104 ∧
      (3*(M : ℝ)^2)^16 / (Real.sqrt M)^104 = 3^16 / (M : ℝ)^20 ∧
      3^16 / (M : ℝ)^20 < 1 := by
  have h := labeling_union_bound_real hM (le_ceil_sqrt_sq M)
  have he := labeling_sqrt_expression (show 0 < M by omega)
  exact ⟨he.symm ▸ h.1, he, h.2⟩

end Internal

end Complexity.BooleanAnalysis.Sensitivity
