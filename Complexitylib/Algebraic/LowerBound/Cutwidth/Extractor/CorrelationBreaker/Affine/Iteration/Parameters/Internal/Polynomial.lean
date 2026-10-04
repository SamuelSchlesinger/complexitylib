/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import Mathlib.Tactic.Ring

/-!
# Polynomial size of the doubled original-source reserve

The new reserve only doubles the existing explicit polynomial bound. Its
source capacity remains a property to prove for a chosen input family.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem double_power (r a b c : Nat) :
    2 * (2 ^ r * a * b * c) = 2 ^ (r + 1) * a * b * c := by
  rw [pow_succ]
  ring

theorem affineIterationParameters_phase_one_reserve (n t a target : Nat) :
    affinePhaseOneSourceEntropy n t a (affineIterationTarget t target) ≤
      affineIterationSourceEntropy n t a target :=
  Nat.le_mul_of_pos_left _ (by decide)

theorem affineIterationParameters_entropy_le (n t a target : Nat) :
    affineIterationSourceEntropy n t a target ≤
      2 ^ 257 * (t + 1) ^ 2 * (a + 1) *
        affinePhaseOneBase n t a (affineIterationTarget t target) ^ 2 := by
  have bound := Nat.mul_le_mul_left 2
    (affinePhaseOneParameters_entropy_le n t a (affineIterationTarget t target))
  rw [double_power] at bound
  simpa only [affineIterationSourceEntropy, Nat.reduceAdd] using bound

end Algebraic.Cutwidth.Extractor.Internal
