/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: uniform sparse bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/UniformSparseBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open Filter
open scoped Topology

namespace DepthThreeLowerBound

/-- A common upper envelope for the sparse-family constants. -/
def sparseEnvelope (b M B d : ℝ) : ℝ :=
  (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2))) / d ^ (1 / 6 : ℝ) +
    (M * b / Real.log 2) * (Real.log d / d ^ (1 / 6 : ℝ)) +
    (1 / (3 * B * Real.log 2)) * (Real.log d / Real.sqrt d)

theorem sparse_expression_le_envelope (b M B d m t : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hB : 0 < B) (hd : 1 ≤ d)
    (hmlo : B * Real.sqrt d / 2 ≤ m) (hmhi : m ≤ 2 * B * Real.sqrt d)
    (htlo : d ^ (1 / 6 : ℝ) / 2 ≤ t) (hthi : t ≤ d ^ (1 / 6 : ℝ))
    (htone : 1 ≤ t) :
    M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t +
        (Real.log t / Real.log 2) / m ≤ sparseEnvelope b M B d := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd
  have hrootpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hroot
  have hpowpos : 0 < d ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hdpos _
  have hhalfpos : 0 < B * Real.sqrt d / 2 := div_pos (mul_pos hB hrootpos) (by norm_num)
  have hmpos : 0 < m := hhalfpos.trans_le hmlo
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one htone
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < 4 * B + 1 := by linarith
  have harg : 2 * m + 1 ≤ (4 * B + 1) * Real.sqrt d := by nlinarith
  have hlog : Real.log (2 * m + 1) ≤ Real.log (4 * B + 1) + Real.log d / 2 := by
    calc
      Real.log (2 * m + 1) ≤ Real.log ((4 * B + 1) * Real.sqrt d) :=
        Real.log_le_log (by linarith) harg
      _ = Real.log (4 * B + 1) + Real.log d / 2 := by
        rw [Real.log_mul hCpos.ne' hrootpos.ne', Real.log_sqrt hdpos.le]
  have hnum0 : 0 ≤ M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) :=
    mul_nonneg hM (add_nonneg zero_le_one
      (mul_nonneg hb (div_nonneg (Real.log_nonneg (by linarith)) hlogtwo.le)))
  have hnum : M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) ≤
      M * (1 + b * ((Real.log (4 * B + 1) + Real.log d / 2) / Real.log 2)) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hlogtwo.le) hb) 1) hM
  have hfirst : M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t ≤
      (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2))) / d ^ (1 / 6 : ℝ) +
        (M * b / Real.log 2) * (Real.log d / d ^ (1 / 6 : ℝ)) := by
    calc
      M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t ≤
          M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) /
            (d ^ (1 / 6 : ℝ) / 2) :=
        div_le_div_of_nonneg_left hnum0 (div_pos hpowpos (by norm_num)) htlo
      _ ≤ M * (1 + b * ((Real.log (4 * B + 1) + Real.log d / 2) / Real.log 2)) /
          (d ^ (1 / 6 : ℝ) / 2) :=
        div_le_div_of_nonneg_right hnum (div_nonneg hpowpos.le (by norm_num))
      _ = _ := by
        field_simp [hpowpos.ne', hlogtwo.ne'] ; ring
  have hlogt : Real.log t ≤ (1 / 6 : ℝ) * Real.log d := by
    calc
      Real.log t ≤ Real.log (d ^ (1 / 6 : ℝ)) := Real.log_le_log htpos hthi
      _ = (1 / 6 : ℝ) * Real.log d := Real.log_rpow hdpos _
  have hsecond : (Real.log t / Real.log 2) / m ≤
      (1 / (3 * B * Real.log 2)) * (Real.log d / Real.sqrt d) := by
    calc
      (Real.log t / Real.log 2) / m ≤
          (Real.log t / Real.log 2) / (B * Real.sqrt d / 2) :=
        div_le_div_of_nonneg_left (div_nonneg (Real.log_nonneg htone) hlogtwo.le)
          hhalfpos hmlo
      _ ≤ (((1 / 6 : ℝ) * Real.log d) / Real.log 2) / (B * Real.sqrt d / 2) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hlogt hlogtwo.le) hhalfpos.le
      _ = _ := by
        field_simp [hB.ne', hrootpos.ne', hlogtwo.ne'] ; ring
  exact add_le_add hfirst hsecond

theorem tendsto_sparseEnvelope (b M B : ℝ) :
    Tendsto (sparseEnvelope b M B) atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun d : ℝ => (d ^ (1 / 6 : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).inv_tendsto_atTop
  have hlog6 : Tendsto (fun d : ℝ => Real.log d / d ^ (1 / 6 : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero
  have hlog2 : Tendsto (fun d : ℝ => Real.log d / Real.sqrt d) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hfirst : Tendsto
      (fun d : ℝ => (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2))) /
        d ^ (1 / 6 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinv.const_mul (2 * M * (1 + b * (Real.log (4 * B + 1) / Real.log 2)))
  have hsecond : Tendsto
      (fun d : ℝ => (M * b / Real.log 2) * (Real.log d / d ^ (1 / 6 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hlog6.const_mul (M * b / Real.log 2)
  have hthird : Tendsto
      (fun d : ℝ => (1 / (3 * B * Real.log 2)) * (Real.log d / Real.sqrt d))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hlog2.const_mul (1 / (3 * B * Real.log 2))
  unfold sparseEnvelope
  simpa only [add_zero] using (hfirst.add hsecond).add hthird

theorem uniform_sparse_condition (b M B : ℝ) (hb : 0 ≤ b) (hM : 0 ≤ M) (hB : 0 < B) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d : ℝ, (D : ℝ) ≤ d → ∀ m t : ℝ,
      B * Real.sqrt d / 2 ≤ m → m ≤ 2 * B * Real.sqrt d →
      d ^ (1 / 6 : ℝ) / 2 ≤ t → t ≤ d ^ (1 / 6 : ℝ) → 1 ≤ t →
      M * (1 + b * (Real.log (2 * m + 1) / Real.log 2)) / t +
        (Real.log t / Real.log 2) / m ≤ 1 / 8 := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_sparseEnvelope b M B).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨D, hD⟩ := exists_nat_ge (max 1 R)
  have hDone : (1 : ℝ) ≤ (D : ℝ) := (le_max_left 1 R).trans hD
  refine ⟨D, by exact_mod_cast hDone, ?_⟩
  intro d hd m t hmlo hmhi htlo hthi htone
  have hd1 : 1 ≤ d := hDone.trans hd
  have hRd : R ≤ d := (le_max_right 1 R).trans (hD.trans hd)
  exact (sparse_expression_le_envelope b M B d m t hb hM hB hd1
    hmlo hmhi htlo hthi htone).trans (hR d hRd).le

theorem hard_slice_tail_bounds (μ m r t : ℝ) (hμ : 0 ≤ μ)
    (hmlo : μ / 2 ≤ m) (hmhi : m ≤ 2 * μ)
    (hr : (33 / 16 : ℝ) * μ ≤ r) (ht : 1 ≤ t) :
    (2 : ℝ) ^ (m - r) ≤ (2 : ℝ) ^ (-μ / 16) ∧
      (2 : ℝ) ^ (-(m * t) / 8) ≤ (2 : ℝ) ^ (-μ / 16) := by
  constructor
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  · have hm : 0 ≤ m := by linarith
    have hprod : 0 ≤ m * (t - 1) := mul_nonneg hm (sub_nonneg.mpr ht)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith

theorem in_window_correlation_bound (μ m : ℝ) (hm : μ / 2 ≤ m) :
    (2 : ℝ) ^ (-m / 8) ≤ (2 : ℝ) ^ (-μ / 16) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

end DepthThreeLowerBound

end

end Complexity
