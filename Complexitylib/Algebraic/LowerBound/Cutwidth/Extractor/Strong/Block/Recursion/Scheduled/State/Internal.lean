/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Unary
import Complexitylib.Classes.P.Iterate
import Complexitylib.Tactic.PolyTime

/-!
# Exact and bounded iteration of the numerical schedule

The division-by-four transition agrees with the entropy formula up to the
scheduled depth. A semiconjugacy transfers this fact to the string program.
Complete iteration uses an explicit bound on every encoded state, supplied
by the finite width theorem for the scheduled specialization.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem scheduledBlockStateStep_iterate (initial h Q E : Nat) {i : Nat} (level : i ≤ h) :
    (scheduledBlockStateStep E)^[i] (initial, recursiveBlockEntropy h Q 0) =
      (recursiveBlockWidth initial h Q E i, recursiveBlockEntropy h Q i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by lia)]
    apply Prod.ext
    · rfl
    · change recursiveBlockEntropy h Q i / 4 = recursiveBlockEntropy h Q (i + 1)
      rw [recursiveBlockEntropy_succ h Q (by lia : i < h)]
      simp

theorem scheduledBlockStateStepEval_mem_FP : scheduledBlockStateStepEval ∈ FP := by
  unfold scheduledBlockStateStepEval
  polytime

theorem scheduledBlockStateStepEval_encode (E : Nat) (state : Nat × Nat) :
    scheduledBlockStateStepEval (encodeScheduledBlockState E state) =
      encodeScheduledBlockState E (scheduledBlockStateStep E state) := by
  simp only [scheduledBlockStateStepEval, encodeScheduledBlockState, scheduledBlockStateStep,
    pairFst_pair, pairSnd_pair, List.length_replicate]

theorem scheduledBlockStateStepEval_iterate (E : Nat) (state : Nat × Nat) (i : Nat) :
    scheduledBlockStateStepEval^[i] (encodeScheduledBlockState E state) =
      encodeScheduledBlockState E ((scheduledBlockStateStep E)^[i] state) := by
  have semiconj : Function.Semiconj (encodeScheduledBlockState E) (scheduledBlockStateStep E)
      scheduledBlockStateStepEval :=
    fun state => (scheduledBlockStateStepEval_encode E state).symm
  exact (semiconj.iterate_right i state).symm

theorem encodeScheduledBlockState_length (E : Nat) (state : Nat × Nat) :
    (encodeScheduledBlockState E state).length = 4 * state.1 + 2 * state.2 + E + 6 := by
  simp only [encodeScheduledBlockState, pair_length, List.length_replicate]
  lia

-- A complete iteration certificate with an explicit bound on every intermediate state.
theorem scheduledBlockState_iterate_mem_FP {initial entropy E count B : List Bool → Nat}
    (hinitial : UnaryFn initial) (hentropy : UnaryFn entropy) (hE : UnaryFn E)
    (hcount : UnaryFn count) (hB : UnaryFn B)
    (bounded : ∀ z j, j ≤ count z →
      ((scheduledBlockStateStep (E z))^[j] (initial z, entropy z)).1 ≤ B z ∧
        ((scheduledBlockStateStep (E z))^[j] (initial z, entropy z)).2 ≤ B z) :
    (fun z => encodeScheduledBlockState (E z)
      ((scheduledBlockStateStep (E z))^[count z] (initial z, entropy z))) ∈ FP := by
  have start : (fun z => encodeScheduledBlockState (E z) (initial z, entropy z)) ∈ FP := by
    unfold encodeScheduledBlockState
    polytime
  have width : UnaryFn fun z => 6 * B z + E z + 6 := by polytime
  have loop := iterate_mem_FP scheduledBlockStateStepEval_mem_FP start hcount.mem_FP width.mem_FP
    (fun z j hj => by
      simp only [List.length_replicate] at hj
      rw [scheduledBlockStateStepEval_iterate, encodeScheduledBlockState_length,
        List.length_replicate]
      have limits := bounded z j hj
      lia)
  refine mem_FP_of_eq loop fun z => ?_
  simp only [List.length_replicate]
  exact scheduledBlockStateStepEval_iterate (E z) (initial z, entropy z) (count z)

-- The proved actual-width bounds discharge every intermediate-state premise.
theorem scheduledBlockState_mem_FP {initial h Q E count : List Bool → Nat}
    (hinitial : UnaryFn initial)
    (hentropy : UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0)
    (hE : UnaryFn E) (hcount : UnaryFn count)
    (capacity : ∀ z, recursiveBlockEntropy (h z) (Q z) 0 ≤ initial z)
    (budget : ∀ z,
      3 * (24 * explicitCondenserBudget (initial z) (recursiveBlockEntropy (h z) (Q z) 0)
        (E z)) + 6 * E z ≤ 2 * Q z)
    (levels : ∀ z, count z ≤ h z) :
    (fun z => encodeScheduledBlockState (E z)
      (recursiveBlockWidth (initial z) (h z) (Q z) (E z) (count z),
        recursiveBlockEntropy (h z) (Q z) (count z))) ∈ FP := by
  have loop := scheduledBlockState_iterate_mem_FP hinitial hentropy hE hcount hinitial
    (fun z j hj => by
      have level : j ≤ h z := hj.trans (levels z)
      rw [scheduledBlockStateStep_iterate (initial z) (h z) (Q z) (E z) level]
      have limits := recursiveBlockWidth_bounds (initial z) (h z) (Q z) (E z)
        (capacity z) (budget z) level
      exact ⟨limits.2, limits.1.trans limits.2⟩)
  refine mem_FP_of_eq loop fun z => ?_
  rw [scheduledBlockStateStep_iterate (initial z) (h z) (Q z) (E z) (levels z)]

-- Cap the power before multiplying by Q; the zero-Q case also remains total.
theorem recursiveBlockEntropy_zero_unaryFn {initial h Q : List Bool → Nat}
    (hinitial : UnaryFn initial) (hh : UnaryFn h) (hQ : UnaryFn Q)
    (capacity : ∀ z, recursiveBlockEntropy (h z) (Q z) 0 ≤ initial z) :
    UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0 := by
  refine (((UnaryFn.const 4).powMin hh hinitial).mul hQ).of_eq fun z => ?_
  simp only [recursiveBlockEntropy, Nat.sub_zero]
  by_cases zero : Q z = 0
  · simp only [zero, Nat.mul_zero]
  · have positive : 1 ≤ Q z := by lia
    have bounded : 4 ^ h z ≤ initial z := by
      calc
        4 ^ h z = 4 ^ h z * 1 := (Nat.mul_one _).symm
        _ ≤ 4 ^ h z * Q z := Nat.mul_le_mul_left _ positive
        _ ≤ initial z := by simpa only [recursiveBlockEntropy, Nat.sub_zero] using capacity z
    rw [min_eq_left bounded]

end Algebraic.Cutwidth.Extractor.Internal
