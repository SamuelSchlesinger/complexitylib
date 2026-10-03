/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Parameters.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Unary
import Complexitylib.Classes.P.Unary
import Complexitylib.Tactic.PolyTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Total initialization with an independent bounded power

Clipping depth to the ceiling input logarithm bounds its fourth power by
`4*(n+1)^2`. This original-input bound certifies the initial entropy before
constructing the compressed width, avoiding a circular capacity argument.
The existing finite reserve theorems then supply all schedule premises.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

private theorem pow_clog_two_le (n : Nat) : 2 ^ Nat.clog 2 (n + 1) ≤ 2 * (n + 1) := by
  by_cases zero : n = 0
  · simp [zero]
  have larger : 1 < n + 1 := by lia
  have lower := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) larger
  have positive := Nat.clog_pos (by decide : 1 < 2) larger
  have exponent : (Nat.clog 2 (n + 1)).pred + 1 = Nat.clog 2 (n + 1) :=
    Nat.succ_pred_eq_of_pos positive
  calc
    2 ^ Nat.clog 2 (n + 1) = 2 ^ (Nat.clog 2 (n + 1)).pred * 2 := by
      rw [← pow_succ, exponent]
    _ ≤ 2 * (n + 1) := by lia

theorem scheduledBlockDepth_pow_four_le (n requested : Nat) :
    4 ^ scheduledBlockDepth n requested ≤ 4 * (n + 1) ^ 2 := by
  have upper : 2 ^ scheduledBlockDepth n requested ≤ 2 * (n + 1) :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.min_le_right requested _)).trans
      (pow_clog_two_le n)
  calc
    4 ^ scheduledBlockDepth n requested = (2 ^ scheduledBlockDepth n requested) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      rfl
    _ ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left upper 2
    _ = 4 * (n + 1) ^ 2 := by ring

theorem scheduledBlockRuntimeInitialWidth_bounds (n requested e : Nat) :
    scheduledBlockInitialEntropy n requested e ≤ scheduledBlockRuntimeInitialWidth n requested e ∧
      scheduledBlockRuntimeInitialWidth n requested e ≤
        64 * scheduledBlockInitialEntropy n requested e :=
  recursiveBlockInitialWidth_bounds n (scheduledBlockInputLog n)
    (scheduledBlockErrorExponent n requested e) (scheduledBlockDepth n requested) le_rfl

theorem scheduledBlockRuntime_reserve_budget (n requested e : Nat) :
    3 * (24 * explicitCondenserBudget (scheduledBlockRuntimeInitialWidth n requested e)
      (scheduledBlockInitialEntropy n requested e) (scheduledBlockErrorExponent n requested e)) +
      6 * scheduledBlockErrorExponent n requested e ≤ 2 * scheduledBlockLeafReserve n requested e :=
  recursiveBlockReserve_budget n (scheduledBlockInputLog n)
    (scheduledBlockErrorExponent n requested e) (scheduledBlockDepth n requested) le_rfl
    (Nat.min_le_right requested _)

variable {n requested e : List Bool → Nat}

theorem scheduledBlockInputLog_unaryFn (hn : UnaryFn n) :
    UnaryFn fun z => scheduledBlockInputLog (n z) := by
  unfold scheduledBlockInputLog
  polytime

theorem scheduledBlockDepth_unaryFn (hn : UnaryFn n) (hrequested : UnaryFn requested) :
    UnaryFn fun z => scheduledBlockDepth (n z) (requested z) :=
  hrequested.min (scheduledBlockInputLog_unaryFn hn)

theorem scheduledBlockErrorExponent_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockErrorExponent (n z) (requested z) (e z) :=
  (he.add (scheduledBlockDepth_unaryFn hn hrequested)).add (UnaryFn.const 2)

theorem scheduledBlockLeafReserve_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockLeafReserve (n z) (requested z) (e z) :=
  (UnaryFn.const 4096).mul
    (((scheduledBlockInputLog_unaryFn hn).add
      (scheduledBlockErrorExponent_unaryFn hn hrequested he)).add (UnaryFn.const 1))

theorem scheduledBlockInitialEntropy_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockInitialEntropy (n z) (requested z) (e z) := by
  have bound : UnaryFn fun z => 4 * (n z + 1) ^ 2 := by polytime
  have power := (UnaryFn.const 4).pow_of_le
    (scheduledBlockDepth_unaryFn hn hrequested) bound
    (fun z => scheduledBlockDepth_pow_four_le (n z) (requested z))
  exact (power.mul (scheduledBlockLeafReserve_unaryFn hn hrequested he)).of_eq fun z => by
    simp only [scheduledBlockInitialEntropy, recursiveBlockEntropy, Nat.sub_zero]

theorem scheduledBlockRuntimeInitialWidth_unaryFn
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    UnaryFn fun z => scheduledBlockRuntimeInitialWidth (n z) (requested z) (e z) := by
  have half := explicitCondenserHalfWidth_unaryFn hn
    (scheduledBlockInitialEntropy_unaryFn hn hrequested he)
    (scheduledBlockErrorExponent_unaryFn hn hrequested he) (UnaryFn.const 1)
  exact half.add half

theorem scheduledBlockStateInit_mem_FP
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e) :
    (fun z => scheduledBlockStateInit (n z) (requested z) (e z)) ∈ FP := by
  have error := scheduledBlockErrorExponent_unaryFn hn hrequested he
  have width := scheduledBlockRuntimeInitialWidth_unaryFn hn hrequested he
  have entropy := scheduledBlockInitialEntropy_unaryFn hn hrequested he
  unfold scheduledBlockStateInit encodeScheduledBlockState
  polytime

theorem scheduledBlockStateInit_iterate_mem_FP {count : List Bool → Nat}
    (hn : UnaryFn n) (hrequested : UnaryFn requested) (he : UnaryFn e)
    (hcount : UnaryFn count) :
    (fun z => scheduledBlockStateStepEval^[min (count z) (scheduledBlockDepth (n z) (requested z))]
      (scheduledBlockStateInit (n z) (requested z) (e z))) ∈ FP := by
  have states := scheduledBlockState_mem_FP
    (initial := fun z => scheduledBlockRuntimeInitialWidth (n z) (requested z) (e z))
    (h := fun z => scheduledBlockDepth (n z) (requested z))
    (Q := fun z => scheduledBlockLeafReserve (n z) (requested z) (e z))
    (E := fun z => scheduledBlockErrorExponent (n z) (requested z) (e z))
    (count := fun z => min (count z) (scheduledBlockDepth (n z) (requested z)))
    (scheduledBlockRuntimeInitialWidth_unaryFn hn hrequested he)
    (scheduledBlockInitialEntropy_unaryFn hn hrequested he)
    (scheduledBlockErrorExponent_unaryFn hn hrequested he)
    (hcount.min (scheduledBlockDepth_unaryFn hn hrequested))
    (fun z => (scheduledBlockRuntimeInitialWidth_bounds (n z) (requested z) (e z)).1)
    (fun z => scheduledBlockRuntime_reserve_budget (n z) (requested z) (e z))
    (fun z => Nat.min_le_right _ _)
  refine mem_FP_of_eq states fun z => ?_
  rw [scheduledBlockStateInit, scheduledBlockStateStepEval_iterate]
  exact congrArg (encodeScheduledBlockState _)
    (scheduledBlockStateStep_iterate
      (scheduledBlockRuntimeInitialWidth (n z) (requested z) (e z))
      (scheduledBlockDepth (n z) (requested z))
      (scheduledBlockLeafReserve (n z) (requested z) (e z))
      (scheduledBlockErrorExponent (n z) (requested z) (e z))
      (Nat.min_le_right (count z) _)).symm

end Algebraic.Cutwidth.Extractor.Internal
