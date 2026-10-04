/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The fixed depth reserve pays every long-row and short-message charge

The logarithmic depth has sixty-four spare levels. Its source threshold
therefore dominates all selected long outputs and all repeated short
observations, even before any advice-dependent slack is used.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineIterationRounds_le (t : Nat) : affineIterationRounds t ≤ t :=
  Nat.clog_le_of_le_pow (show t + 1 ≤ 2 ^ t from Nat.lt_two_pow_self)

theorem affineIterationRounds_cover (t : Nat) : t + 1 ≤ 2 ^ affineIterationRounds t :=
  Nat.le_pow_clog (by decide) _

theorem affineIteration_long_reserve (t L : Nat) :
    t * matchedBlockOutputBits (growingMatchedBlockDepth t) L +
      2 * affineIterationRounds t * ((t + 1) * matchedBlockSeedBits L) ≤
        2 ^ (2 * growingMatchedBlockDepth t + 14) * L := by
  let R := affineIterationRounds t
  have ht : t ≤ 2 ^ R := (Nat.le_succ t).trans (affineIterationRounds_cover t)
  have ht₁ : t + 1 ≤ 2 ^ R := affineIterationRounds_cover t
  have hr : R ≤ 2 ^ R := (Nat.lt_two_pow_self).le
  have h : growingMatchedBlockDepth t = R + 64 := rfl
  have pieces : t * 2 ^ growingMatchedBlockDepth t + 2 * R * (t + 1) * 2 ^ 24 ≤
      2 ^ (2 * growingMatchedBlockDepth t + 14) := by
    calc
      _ ≤ 2 ^ R * (2 ^ R * 2 ^ 64) + 2 * 2 ^ R * 2 ^ R * 2 ^ 24 := by
        rw [h, pow_add]
        exact Nat.add_le_add (Nat.mul_le_mul_right _ ht)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr) ht₁))
      _ = (2 ^ 64 + 2 ^ 25) * (2 ^ R) ^ 2 := by norm_num; ring
      _ ≤ 2 ^ 142 * (2 ^ R) ^ 2 := by
        exact Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by
        rw [h, show 2 * (R + 64) + 14 = R * 2 + 142 by lia, pow_add, pow_mul]
        ring
  convert Nat.mul_le_mul_right L pieces using 1
  simp only [matchedBlockOutputBits, matchedBlockSeedBits]
  ring

theorem affineIteration_merge_reserve (t L e : Nat) (error : e ≤ L) :
    2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits (growingMatchedBlockDepth t) L := by
  have bound := matchedBlockOutputBits_merging_reserve t L e error
  change 2 ^ 62 * L + (2 * t + 2) * matchedBlockSeedBits L + e ≤
    matchedBlockOutputBits (growingMatchedBlockDepth t) L at bound
  have step := Nat.mul_le_mul_right (matchedBlockSeedBits L)
    (show t + t + 1 ≤ 2 * t + 2 by lia)
  lia

end Algebraic.Cutwidth.Extractor.Internal
