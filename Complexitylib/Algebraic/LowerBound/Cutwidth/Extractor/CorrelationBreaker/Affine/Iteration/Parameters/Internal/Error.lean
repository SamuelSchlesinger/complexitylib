/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The boosted local error pays the complete doubling recurrence

The exact recurrence is `ρ ↦ 2ρ + 8 * 2⁻ᵉ`. The first-phase target has
one spare bit beyond the number of rounds, and the local exponent has
three additional bits for the factor eight.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineIterationParameters_error_budget (t target : Nat) :
    let R := affineIterationRounds t
    let σ := affineIterationTarget t target
    (2 : ℝ) ^ R * ((2 : ℝ) ^ σ)⁻¹ +
      8 * ((2 : ℝ) ^ R - 1) * ((2 : ℝ) ^ affinePhaseOneLocalError σ)⁻¹ ≤
        ((2 : ℝ) ^ target)⁻¹ := by
  let R := affineIterationRounds t
  let σ := affineIterationTarget t target
  have error : 8 * ((2 : ℝ) ^ affinePhaseOneLocalError σ)⁻¹ =
      ((2 : ℝ) ^ σ)⁻¹ := by
    simp only [affinePhaseOneLocalError, pow_add, mul_inv_rev]
    norm_num
    ring
  change (2 : ℝ) ^ R * ((2 : ℝ) ^ σ)⁻¹ +
    8 * ((2 : ℝ) ^ R - 1) * ((2 : ℝ) ^ affinePhaseOneLocalError σ)⁻¹ ≤ _
  calc
    _ = (2 * (2 : ℝ) ^ R - 1) * ((2 : ℝ) ^ σ)⁻¹ := by
      rw [show 8 * ((2 : ℝ) ^ R - 1) * ((2 : ℝ) ^ affinePhaseOneLocalError σ)⁻¹ =
        ((2 : ℝ) ^ R - 1) * (8 * ((2 : ℝ) ^ affinePhaseOneLocalError σ)⁻¹) by ring, error]
      ring
    _ ≤ (2 * (2 : ℝ) ^ R) * ((2 : ℝ) ^ σ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ((2 : ℝ) ^ target)⁻¹ := by
      dsimp only [σ, affineIterationTarget, R]
      rw [pow_add, pow_add]
      norm_num
      field_simp

end Algebraic.Cutwidth.Extractor.Internal
