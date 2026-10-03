/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Extraction.Defs
import Mathlib.Tactic.Linarith

/-!
# Finite dyadic reserves for one subset-union round

Each of the four source charges fits one local extractor error under an
explicit natural-number reserve. Adding the four actual extractor errors
gives eight local errors, in addition to the two previous discrepancies.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem capped_mass_term (a e k : Nat) {mass : ℝ}
    (reserve : a + e ≤ k) (source : mass ≤ ((2 : ℝ) ^ k)⁻¹) :
    (2 : ℝ) ^ a * mass ≤ ((2 : ℝ) ^ e)⁻¹ := by
  apply (mul_le_mul_of_nonneg_left source (by positivity)).trans
  rw [mul_inv_le_iff₀ (by positivity), le_inv_mul_iff₀ (by positivity), ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by lia)

theorem affineRoundError_dyadic_le (t h L e s u kx ky : Nat)
    (ρS ρT : ℝ) {leftMass rightMass : ℝ}
    (first : 2 ^ 62 * L + (s + t + 1) * matchedBlockSeedBits L + e ≤ ky)
    (merge : 2 ^ 62 * L + (s + t + 1) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits h L)
    (recover : 2 ^ 62 * L + (u + 3 * (t + 1)) * matchedBlockSeedBits L + e ≤ ky)
    (final : 2 ^ (2 * h + 14) * L + u * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L + e ≤ kx)
    (left : leftMass ≤ ((2 : ℝ) ^ kx)⁻¹)
    (right : rightMass ≤ ((2 : ℝ) ^ ky)⁻¹) :
    affineRoundError t h L e s u ρS ρT leftMass rightMass ≤
      ρS + ρT + 8 * ((2 : ℝ) ^ e)⁻¹ := by
  have first_bound := capped_mass_term _ _ _ first right
  have merge_bound := capped_mass_term _ _ _ merge le_rfl
  have recover_bound := capped_mass_term _ _ _ recover right
  have final_bound := capped_mass_term _ _ _ final left
  unfold affineRoundError
  rw [div_eq_mul_inv]
  linarith

end Algebraic.Cutwidth.Extractor.Internal
