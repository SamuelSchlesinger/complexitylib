/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Reserves
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Every selected round satisfies all four extraction reserves

The global budgets include the entire current round. Subtracting only the
observations from earlier rounds leaves the first, middle, recovery, and
final charges required by the actual subset-doubling theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem remaining_charge {factor rounds message observed reserve charge total i : Nat}
    (budget : observed + factor * rounds * message + reserve ≤ total)
    (current : charge ≤ factor * message + reserve) (index : i < rounds) :
    charge ≤ total - (observed + factor * i * message) := by
  have count := Nat.mul_le_mul_right message
    (Nat.mul_le_mul_left factor (Nat.succ_le_of_lt index))
  simp only [Nat.succ_eq_add_one, mul_add, add_mul, mul_one] at count
  lia

private theorem remaining_capacity {factor rounds message observed reserve total i : Nat}
    (budget : observed + factor * rounds * message + reserve ≤ total)
    (index : i ≤ rounds) : observed + factor * i * message ≤ total := by
  have count := Nat.mul_le_mul_right message (Nat.mul_le_mul_left factor index)
  lia

theorem affineIterationParameters_left_capacity (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    affineIterationInitialLeftLoss n t a target +
      2 * i * affineIterationMessageBits n t a target ≤
        affineIterationSourceEntropy n t a target := by
  apply remaining_capacity (reserve :=
    2 ^ (2 * growingMatchedBlockDepth t + 14) *
      affinePhaseOneScale n t a (affineIterationTarget t target) +
    t * matchedBlockOutputBits (growingMatchedBlockDepth t)
      (affinePhaseOneScale n t a (affineIterationTarget t target)) +
    affinePhaseOneLocalError (affineIterationTarget t target)) _ index
  simpa only [add_assoc] using affineIterationParameters_left_budget n t a target

theorem affineIterationParameters_right_capacity (n t a target : Nat) {i : Nat}
    (index : i ≤ affineIterationRounds t) :
    affineIterationInitialRightLoss n t a target +
      4 * i * affineIterationMessageBits n t a target ≤
        affinePhaseOneRightBits n t a (affineIterationTarget t target) := by
  apply remaining_capacity (reserve :=
    2 ^ 62 * affinePhaseOneScale n t a (affineIterationTarget t target) +
    affinePhaseOneLocalError (affineIterationTarget t target)) _ index
  simpa only [add_assoc] using affineIterationParameters_right_budget n t a target

private theorem right_reserve (n t a target count : Nat) {i : Nat}
    (index : i < affineIterationRounds t) (count_bound : count ≤ 4 * (t + 1)) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    2 ^ 62 * L + count * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
      affineIterationRightEntropy n t a target i := by
  let σ := affineIterationTarget t target
  let L := affinePhaseOneScale n t a σ
  apply remaining_charge (factor := 4) (rounds := affineIterationRounds t)
    (reserve := 2 ^ 62 * L + affinePhaseOneLocalError σ) _ _ index
  · simpa only [add_assoc] using affineIterationParameters_right_budget n t a target
  · have count := Nat.mul_le_mul_right (matchedBlockSeedBits L) count_bound
    change _ ≤ 4 * ((t + 1) * matchedBlockSeedBits L) +
      (2 ^ 62 * L + affinePhaseOneLocalError σ)
    calc
      _ ≤ 2 ^ 62 * L + (4 * (t + 1) * matchedBlockSeedBits L) +
          affinePhaseOneLocalError σ := Nat.add_le_add_right (Nat.add_le_add_left count _) _
      _ = _ := by ring

theorem affineIterationParameters_first_reserve (n t a target : Nat) {i : Nat}
    (index : i < affineIterationRounds t) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
      affineIterationRightEntropy n t a target i :=
  right_reserve n t a target (t + t + 1) index (by lia)

theorem affineIterationParameters_merge_reserve (n t a target : Nat) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
      matchedBlockOutputBits (growingMatchedBlockDepth t) L := by
  apply affineIteration_merge_reserve
  have guard := affinePhaseOneParameters_growing_guard n t a (affineIterationTarget t target)
  exact (Nat.le_add_right _ (growingMatchedBlockDepth t)).trans
    ((Nat.le_add_right _ 2).trans guard.2.1)

theorem affineIterationParameters_recover_reserve (n t a target : Nat) {i : Nat}
    (index : i < affineIterationRounds t) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    2 ^ 62 * L + (t + 3 * (t + 1)) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
      affineIterationRightEntropy n t a target i :=
  right_reserve n t a target (t + 3 * (t + 1)) index (by lia)

theorem affineIterationParameters_final_reserve (n t a target : Nat) {i : Nat}
    (index : i < affineIterationRounds t) :
    let σ := affineIterationTarget t target
    let L := affinePhaseOneScale n t a σ
    let h := growingMatchedBlockDepth t
    2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L + affinePhaseOneLocalError σ ≤
        affineIterationLeftEntropy n t a target i := by
  let σ := affineIterationTarget t target
  let L := affinePhaseOneScale n t a σ
  let h := growingMatchedBlockDepth t
  apply remaining_charge (factor := 2) (rounds := affineIterationRounds t)
    (reserve := 2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L +
      affinePhaseOneLocalError σ) _ _ index
  · simpa only [add_assoc] using affineIterationParameters_left_budget n t a target
  · apply le_of_eq
    dsimp only [affineIterationMessageBits, σ, L, h]
    ring

end Algebraic.Cutwidth.Extractor.Internal
