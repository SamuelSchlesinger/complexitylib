/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The unchanged chooser pays all cumulative source losses

Double the original left reserve. The existing original-right width has an
extra common-base factor, which pays four short-message families in each
round. Both inequalities include the complete first-phase transcript.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem doubled_reserve {initial threshold output observed error repeated extra : Nat}
    (bound : output + repeated ≤ threshold) :
    observed + repeated + threshold + output + error ≤
      2 * (initial + (threshold + extra + observed) + error) := by
  lia

theorem affineIterationParameters_left_budget (n t a target : Nat) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    let h := growingMatchedBlockDepth t
    affineIterationInitialLeftLoss n t a target +
      2 * affineIterationRounds t * affineIterationMessageBits n t a target +
      2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L + affinePhaseOneLocalError σ ≤
        affineIterationSourceEntropy n t a target := by
  have bound := affineIteration_long_reserve t
    (affinePhaseOneScale n t a (affineIterationTarget t target))
  exact doubled_reserve bound

theorem affineIterationParameters_right_budget (n t a target : Nat) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    affineIterationInitialRightLoss n t a target +
      4 * affineIterationRounds t * affineIterationMessageBits n t a target +
      2 ^ 62 * L + affinePhaseOneLocalError σ ≤ affinePhaseOneRightBits n t a σ := by
  let σ := affineIterationTarget t target
  let B := affinePhaseOneBase n t a σ
  let L := affinePhaseOneScale n t a σ
  let P := (t + 1) * (a + 1) * L
  let A := B * P
  have base : 256 ≤ B := by dsimp only [B, affinePhaseOneBase]; lia
  have lp : 0 < L := by
    change 0 < 2 ^ 20 * B ^ 2
    positivity
  have pp : 0 < P := by dsimp only [P]; positivity
  have pa : P ≤ A := Nat.le_mul_of_pos_left P (by lia : 0 < B)
  have la : L ≤ A :=
    (Nat.le_mul_of_pos_left L (by positivity : 0 < (t + 1) * (a + 1))).trans pa
  have ba : B ≤ A := Nat.le_mul_of_pos_right B pp
  have short : (t + 1) * L ≤ P := by
    simpa only [P, mul_assoc, mul_left_comm, mul_comm] using
      Nat.le_mul_of_pos_left ((t + 1) * L) (show 0 < a + 1 by lia)
  have rounds : affineIterationRounds t ≤ B := by
    dsimp only [B, affinePhaseOneBase, affineIterationRounds]
    lia
  have error : affinePhaseOneLocalError σ ≤ A := by
    apply le_trans ?_ ba
    dsimp only [affinePhaseOneLocalError, B, affinePhaseOneBase]
    lia
  have initial : affineIterationInitialRightLoss n t a target ≤
      (2 ^ 114 + 2 ^ 154 + 2 ^ 24) * A := by
    calc
      _ = (2 ^ 114 + 2 ^ 154) * P + 2 ^ 24 * ((t + 1) * L) := by
        dsimp only [affineIterationInitialRightLoss, matchedBlockSeedBits,
          matchedBlockOutputBits, affinePhaseOneInitialScale, P, L, σ]
        norm_num
        ring
      _ ≤ (2 ^ 114 + 2 ^ 154) * A + 2 ^ 24 * A :=
        Nat.add_le_add (Nat.mul_le_mul_left _ pa) (Nat.mul_le_mul_left _ (short.trans pa))
      _ = _ := by ring
  have repeated : 4 * affineIterationRounds t * affineIterationMessageBits n t a target ≤
      2 ^ 26 * A := by
    calc
      _ = 2 ^ 26 * (affineIterationRounds t * ((t + 1) * L)) := by
        dsimp only [affineIterationMessageBits, matchedBlockSeedBits, L, σ]
        norm_num
        ring
      _ ≤ 2 ^ 26 * (B * P) := Nat.mul_le_mul_left _ (Nat.mul_le_mul rounds short)
      _ = _ := rfl
  have threshold : 2 ^ 62 * L ≤ 2 ^ 62 * A := Nat.mul_le_mul_left _ la
  have constants : 2 ^ 114 + 2 ^ 154 + 2 ^ 24 + 2 ^ 26 + 2 ^ 62 + 1 ≤ (2 : Nat) ^ 160 := by
    norm_num
  have bound := Nat.mul_le_mul_right A constants
  change _ ≤ affinePhaseOneRightBits n t a σ
  calc
    _ ≤ (2 ^ 114 + 2 ^ 154 + 2 ^ 24) * A + 2 ^ 26 * A + 2 ^ 62 * A + A :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add initial repeated) threshold) error
    _ = (2 ^ 114 + 2 ^ 154 + 2 ^ 24 + 2 ^ 26 + 2 ^ 62 + 1) * A := by ring
    _ ≤ 2 ^ 160 * A := bound
    _ = _ := by dsimp only [A, P, B, L, affinePhaseOneRightBits]; ring

end Algebraic.Cutwidth.Extractor.Internal
