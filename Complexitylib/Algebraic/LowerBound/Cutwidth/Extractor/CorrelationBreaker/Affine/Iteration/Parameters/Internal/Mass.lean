/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Round
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact mass bounds after the full observed transcript

Two left-message families and four right-message families are observed in
each actual round. The finite capacities ensure that natural subtraction
in the remaining entropy agrees exactly with the dyadic envelope mass.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem observed_mass (total observed message factor i : Nat)
    (capacity : observed + factor * i * message ≤ total) :
    ((2 : ℝ) ^ message) ^ (factor * i) *
      ((2 : ℝ) ^ observed * ((2 : ℝ) ^ total)⁻¹) =
        ((2 : ℝ) ^ (total - (observed + factor * i * message)))⁻¹ := by
  have powers : ((2 : ℝ) ^ message) ^ (factor * i) * (2 : ℝ) ^ observed =
      (2 : ℝ) ^ (observed + factor * i * message) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [← mul_assoc, powers]
  have total_power : (2 : ℝ) ^ total =
      (2 : ℝ) ^ (observed + factor * i * message) *
        (2 : ℝ) ^ (total - (observed + factor * i * message)) := by
    rw [← pow_add, Nat.add_sub_of_le capacity]
  rw [total_power]
  field_simp

theorem affineIterationParameters_left_mass (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    ((2 : ℝ) ^ affineIterationMessageBits n t a target) ^ (2 * i) *
      ((2 : ℝ) ^ affineIterationInitialLeftLoss n t a target *
        ((2 : ℝ) ^ affineIterationSourceEntropy n t a target)⁻¹) =
      ((2 : ℝ) ^ affineIterationLeftEntropy n t a target i)⁻¹ :=
  observed_mass _ _ _ 2 i (affineIterationParameters_left_capacity n t a target index)

theorem affineIterationParameters_right_mass (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    ((2 : ℝ) ^ affineIterationMessageBits n t a target) ^ (4 * i) *
      ((2 : ℝ) ^ affineIterationInitialRightLoss n t a target *
        ((2 : ℝ) ^ affinePhaseOneRightBits n t a (affineIterationTarget t target))⁻¹) =
      ((2 : ℝ) ^ affineIterationRightEntropy n t a target i)⁻¹ :=
  observed_mass _ _ _ 4 i (affineIterationParameters_right_capacity n t a target index)

end Algebraic.Cutwidth.Extractor.Internal
