/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Splitting
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Unary
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Classes.P.Iterate
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime

/-!
# Correct and bounded encoded iteration of block payloads

The total encoded step agrees with the structured step. Its numerical
projection follows the checked schedule, the count doubles, and the exact
output length gives the payload bound even for arbitrary input and seed
words. The unused seed suffix can only shrink. Together these facts bound
every intermediate encoded state and justify the complete FP iteration.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem scheduledBlockRunStepEval_encode (E : Nat) (state : ScheduledBlockRunState) :
    scheduledBlockRunStepEval (encodeScheduledBlockRun E state) =
      encodeScheduledBlockRun E (scheduledBlockRunStep E state) := by
  simp only [scheduledBlockRunStepEval, encodeScheduledBlockRun, scheduledBlockRunStep,
    scheduledBlockStateStepEval, encodeScheduledBlockState, scheduledBlockStateStep,
    pairFst_pair, pairSnd_pair, List.length_replicate]

theorem scheduledBlockRunStepEval_iterate (E : Nat) (state : ScheduledBlockRunState) (i : Nat) :
    scheduledBlockRunStepEval^[i] (encodeScheduledBlockRun E state) =
      encodeScheduledBlockRun E ((scheduledBlockRunStep E)^[i] state) := by
  have semiconj : Function.Semiconj (encodeScheduledBlockRun E)
      (scheduledBlockRunStep E) scheduledBlockRunStepEval :=
    fun state => (scheduledBlockRunStepEval_encode E state).symm
  exact (semiconj.iterate_right i state).symm

theorem encodeScheduledBlockRun_length (E : Nat) (state : ScheduledBlockRunState) :
    (encodeScheduledBlockRun E state).length =
      8 * state.dimensions.1 + 4 * state.dimensions.2 + 2 * E + 2 * state.count +
        2 * state.payload.length + state.seeds.length + 18 := by
  simp only [encodeScheduledBlockRun, pair_length, encodeScheduledBlockState_length,
    List.length_replicate]
  lia

theorem scheduledBlockRunStep_iterate_dimensions (E : Nat) (state : ScheduledBlockRunState)
    (i : Nat) :
    ((scheduledBlockRunStep E)^[i] state).dimensions =
      (scheduledBlockStateStep E)^[i] state.dimensions := by
  exact (show Function.Semiconj ScheduledBlockRunState.dimensions
    (scheduledBlockRunStep E) (scheduledBlockStateStep E) from fun _ => rfl).iterate_right i state

theorem scheduledBlockRunStep_iterate_count (E : Nat) (state : ScheduledBlockRunState)
    (i : Nat) : ((scheduledBlockRunStep E)^[i] state).count = 2 ^ i * state.count := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    change 2 * ((scheduledBlockRunStep E)^[i] state).count = _
    rw [ih, pow_succ]
    ring

theorem scheduledBlockRunStep_iterate_seeds_length (E : Nat) (state : ScheduledBlockRunState)
    (i : Nat) : ((scheduledBlockRunStep E)^[i] state).seeds.length ≤ state.seeds.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    simp only [scheduledBlockRunStep, List.length_drop]
    exact (Nat.sub_le _ _).trans ih

private theorem scheduledBlockRunStep_payload_length (E : Nat) (state : ScheduledBlockRunState) :
    (scheduledBlockRunStep E state).payload.length =
      (scheduledBlockRunStep E state).count * (scheduledBlockRunStep E state).dimensions.1 := by
  simp only [scheduledBlockRunStep, scheduledBlockStateStep,
    explicitBlockCondenserBits_length, List.length_replicate]
  rw [← explicitCondenserHalfWidth_double]
  ring

theorem scheduledBlockRunStep_iterate_payload_length (E : Nat) (state : ScheduledBlockRunState)
    (shape : state.payload.length = state.count * state.dimensions.1) (i : Nat) :
    ((scheduledBlockRunStep E)^[i] state).payload.length =
      ((scheduledBlockRunStep E)^[i] state).count *
        ((scheduledBlockRunStep E)^[i] state).dimensions.1 := by
  cases i with
  | zero => exact shape
  | succ i =>
    rw [Function.iterate_succ_apply']
    exact scheduledBlockRunStep_payload_length E _

theorem scheduledBlockRunInitial_payload_length (n h Q E : Nat) (source seeds : List Bool) :
    (scheduledBlockRunInitial n h Q E source seeds).payload.length =
      scheduledBlockInitialWidth n h Q E := by
  simp only [scheduledBlockRunInitial, explicitCondenserBits_length,
    scheduledBlockInitialWidth, explicitCondenserHalfWidth_double]

theorem scheduledBlockRun_dimensions (n h Q E : Nat) (source seeds : List Bool) :
    (scheduledBlockRun n h Q E source seeds).dimensions =
      (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h, Q) := by
  rw [scheduledBlockRun, scheduledBlockRunStep_iterate_dimensions]
  change (scheduledBlockStateStep E)^[h]
    (scheduledBlockInitialWidth n h Q E, recursiveBlockEntropy h Q 0) = _
  rw [scheduledBlockStateStep_iterate (scheduledBlockInitialWidth n h Q E) h Q E le_rfl,
    recursiveBlockEntropy_last]

theorem scheduledBlockRun_count (n h Q E : Nat) (source seeds : List Bool) :
    (scheduledBlockRun n h Q E source seeds).count = 2 ^ h := by
  simp only [scheduledBlockRun, scheduledBlockRunStep_iterate_count,
    scheduledBlockRunInitial, Nat.mul_one]

theorem scheduledBlockRun_iterate_bound (n h Q E : Nat) (source seeds : List Bool)
    (positive : 0 < Q)
    (budget : 3 * (24 * explicitCondenserBudget (scheduledBlockInitialWidth n h Q E)
      (recursiveBlockEntropy h Q 0) E) + 6 * E ≤ 2 * Q)
    {i : Nat} (level : i ≤ h) :
    (encodeScheduledBlockRun E
      ((scheduledBlockRunStep E)^[i] (scheduledBlockRunInitial n h Q E source seeds))).length ≤
      18 * scheduledBlockInitialWidth n h Q E + 2 * E + seeds.length + 18 := by
  let initial := scheduledBlockInitialWidth n h Q E
  let state := scheduledBlockRunInitial n h Q E source seeds
  have capacity : recursiveBlockEntropy h Q 0 ≤ initial :=
    explicitCondenserHalfWidth_capacity n (recursiveBlockEntropy h Q 0) E (by decide : 0 < 1)
  have dimensions : ((scheduledBlockRunStep E)^[i] state).dimensions =
      (recursiveBlockWidth initial h Q E i, recursiveBlockEntropy h Q i) := by
    rw [scheduledBlockRunStep_iterate_dimensions]
    exact scheduledBlockStateStep_iterate initial h Q E level
  have count : ((scheduledBlockRunStep E)^[i] state).count = 2 ^ i := by
    rw [scheduledBlockRunStep_iterate_count]
    simp only [state, scheduledBlockRunInitial, Nat.mul_one]
  have shape : state.payload.length = state.count * state.dimensions.1 := by
    simpa only [state, scheduledBlockRunInitial, Nat.one_mul] using
      scheduledBlockRunInitial_payload_length n h Q E source seeds
  have payload := scheduledBlockRunStep_iterate_payload_length E state shape i
  rw [dimensions, count] at payload
  have widths := recursiveBlockWidth_bounds initial h Q E capacity budget level
  have counts := (recursiveBlock_count_le h Q positive level).trans capacity
  have payloads := recursiveBlock_payload_le initial h Q E capacity budget level
  have suffix := scheduledBlockRunStep_iterate_seeds_length E state i
  have startSuffix : state.seeds.length ≤ seeds.length := by
    simp only [state, scheduledBlockRunInitial, List.length_drop]
    exact Nat.sub_le _ _
  change (encodeScheduledBlockRun E ((scheduledBlockRunStep E)^[i] state)).length ≤ _
  rw [encodeScheduledBlockRun_length, dimensions, count, payload]
  dsimp only at widths ⊢
  lia

theorem scheduledBlockRunStepEval_mem_FP : scheduledBlockRunStepEval ∈ FP := by
  unfold scheduledBlockRunStepEval
  polytime

theorem scheduledBlockRun_mem_FP {n h Q E : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hn : UnaryFn n)
    (hentropy : UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0)
    (hh : UnaryFn h) (hE : UnaryFn E) (hsource : source ∈ FP) (hseeds : seeds ∈ FP)
    (positive : ∀ z, 0 < Q z)
    (budget : ∀ z, 3 * (24 * explicitCondenserBudget
      (scheduledBlockInitialWidth (n z) (h z) (Q z) (E z))
      (recursiveBlockEntropy (h z) (Q z) 0) (E z)) + 6 * E z ≤ 2 * Q z) :
    (fun z => encodeScheduledBlockRun (E z)
      (scheduledBlockRun (n z) (h z) (Q z) (E z) (source z) (seeds z))) ∈ FP := by
  have initialWidth : UnaryFn fun z => scheduledBlockInitialWidth (n z) (h z) (Q z) (E z) := by
    unfold scheduledBlockInitialWidth
    polytime
  have start : (fun z => encodeScheduledBlockRun (E z)
      (scheduledBlockRunInitial (n z) (h z) (Q z) (E z) (source z) (seeds z))) ∈ FP := by
    unfold encodeScheduledBlockRun encodeScheduledBlockState scheduledBlockRunInitial
    polytime
  have width : UnaryFn fun z =>
      18 * scheduledBlockInitialWidth (n z) (h z) (Q z) (E z) +
        2 * E z + (seeds z).length + 18 := by polytime
  have loop := iterate_mem_FP scheduledBlockRunStepEval_mem_FP start hh.mem_FP width.mem_FP
    (fun z i hi => by
      simp only [List.length_replicate] at hi
      rw [scheduledBlockRunStepEval_iterate, List.length_replicate]
      exact scheduledBlockRun_iterate_bound (n z) (h z) (Q z) (E z)
        (source z) (seeds z) (positive z) (budget z) hi)
  refine mem_FP_of_eq loop fun z => ?_
  simp only [List.length_replicate, scheduledBlockRun]
  exact scheduledBlockRunStepEval_iterate (E z) _ (h z)

end Algebraic.Cutwidth.Extractor.Internal
