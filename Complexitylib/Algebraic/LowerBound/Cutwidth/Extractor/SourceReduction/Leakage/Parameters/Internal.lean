/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters

/-!
# A finite polynomial bound including leakage

The affine reserve is quadratic in the common logarithmic base and each
seed-width observation is cubic. Their sum obeys a single cubic bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem add_powers_le (a b : Nat) (order : b ≤ a) :
    (2 : Nat) ^ a + 2 ^ b ≤ 2 ^ (a + 1) := by
  calc
    _ ≤ 2 ^ a + 2 ^ a := Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) order) _
    _ = 2 ^ (a + 1) := by rw [pow_succ, mul_two]

private theorem mul_polynomial_le {a b c : Nat} (bound : a + b ≤ c) (x y z : Nat) :
    a * x * y * z + b * x * y * z ≤ c * x * y * z := by
  calc
    _ = (a + b) * x * y * z := by ring
    _ ≤ c * x * y * z := Nat.mul_le_mul_right z
      (Nat.mul_le_mul_right y (Nat.mul_le_mul_right x bound))

theorem affineLeakageSourceEntropy_le (n t a target : Nat) :
    affineLeakageSourceEntropy n t a target ≤
      2 ^ 258 * (t + 1) ^ 2 * (a + 1) *
        affinePhaseOneBase n t a (affineIterationTarget t target) ^ 3 := by
  let B := affinePhaseOneBase n t a (affineIterationTarget t target)
  have positive : 1 ≤ B := by
    dsimp [B, affinePhaseOneBase]
    lia
  have square_le : B ^ 2 ≤ B ^ 3 := by
    calc
      B ^ 2 = B ^ 2 * 1 := by simp
      _ ≤ B ^ 2 * B := Nat.mul_le_mul_left _ positive
      _ = B ^ 3 := by ring
  have old := affineIterationParameters_entropy_le n t a target
  change affineIterationSourceEntropy n t a target ≤
    2 ^ 257 * (t + 1) ^ 2 * (a + 1) * B ^ 2 at old
  have leakage : (t + 1) *
      affinePhaseOneRightBits n t a (affineIterationTarget t target) =
        2 ^ 180 * (t + 1) ^ 2 * (a + 1) * B ^ 3 := by
    simp only [affinePhaseOneRightBits, affinePhaseOneScale]
    dsimp [B]
    ring
  unfold affineLeakageSourceEntropy
  rw [leakage]
  calc
    _ ≤ 2 ^ 257 * (t + 1) ^ 2 * (a + 1) * B ^ 3 +
        2 ^ 180 * (t + 1) ^ 2 * (a + 1) * B ^ 3 :=
      Nat.add_le_add_right (old.trans (Nat.mul_le_mul_left _ square_le)) _
    _ ≤ 2 ^ 258 * (t + 1) ^ 2 * (a + 1) * B ^ 3 := by
      have constants : (2 : Nat) ^ 257 + 2 ^ 180 ≤ 2 ^ 258 := by
        simpa only [Nat.reduceAdd] using add_powers_le 257 180 (by decide)
      exact mul_polynomial_le constants ((t + 1) ^ 2) (a + 1) (B ^ 3)

end Algebraic.Cutwidth.Extractor.Internal
