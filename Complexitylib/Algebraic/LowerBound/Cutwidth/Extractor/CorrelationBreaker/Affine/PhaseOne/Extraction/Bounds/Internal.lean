/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Defs
import Mathlib.Tactic.Linarith

/-!
# A dyadic budget for the complete first affine phase

Two original-source mass terms and three local errors fit the requested
error after increasing each local exponent by three. The two explicit
natural-number reserves account for the actual observed output lengths.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem capped_mass_term (a e k : Nat) {mass : ℝ}
    (reserve : a + e ≤ k) (source : mass ≤ ((2 : ℝ) ^ k)⁻¹) :
    (2 : ℝ) ^ a * mass ≤ ((2 : ℝ) ^ e)⁻¹ := by
  apply (mul_le_mul_of_nonneg_left source (by positivity)).trans
  rw [mul_inv_le_iff₀ (by positivity), le_inv_mul_iff₀ (by positivity), ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by lia)

theorem affinePhaseOneError_dyadic_le (t h L₀ L₁ target k : Nat) {mass : ℝ}
    (initial : 2 ^ 142 * L₀ + (target + 3) ≤ k)
    (final : 2 ^ (2 * h + 14) * L₁ + matchedBlockOutputBits h L₁ +
      (t + 1) * matchedBlockOutputBits 64 L₀ + (target + 3) ≤ k)
    (source : mass ≤ ((2 : ℝ) ^ k)⁻¹) :
    affinePhaseOneError t h L₀ (target + 3) L₁ (target + 3) (target + 3) mass ≤
      ((2 : ℝ) ^ target)⁻¹ := by
  have first := capped_mass_term _ _ _ initial source
  have last := capped_mass_term _ _ _ final source
  unfold affinePhaseOneError
  calc
    _ ≤ 5 * ((2 : ℝ) ^ (target + 3))⁻¹ := by linarith
    _ ≤ ((2 : ℝ) ^ target)⁻¹ := by
      rw [pow_add, mul_inv_rev]
      norm_num
      have positive : 0 ≤ ((2 : ℝ) ^ target)⁻¹ := by positivity
      linarith

end Algebraic.Cutwidth.Extractor.Internal
