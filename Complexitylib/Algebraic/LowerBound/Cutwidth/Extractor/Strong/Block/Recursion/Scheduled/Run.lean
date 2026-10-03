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
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run.Internal

/-!
# Uniform bounded evaluation of all internal block levels

The actual block payload and seed-consumption loop is polynomial-time
uniformly in its unary parameters and input words, provided the supplied
entropy schedule satisfies the proved global reserve budget and has a
positive leaf reserve. Every intermediate encoding is bounded by eighteen
times the initial compressed width, twice the error exponent, the original
seed-word length, and a constant.

The proof certifies the complete iteration, including all numerical values,
block counts, payloads, and unused seeds. The exact statistical meaning of
canonical seed words and the final leaf extraction are separate layers.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The encoded runtime step computes the structured block and seed update. -/
theorem scheduledBlockRunStepEval_encode (E : Nat) (state : ScheduledBlockRunState) :
    scheduledBlockRunStepEval (encodeScheduledBlockRun E state) =
      encodeScheduledBlockRun E (scheduledBlockRunStep E state) :=
  Internal.scheduledBlockRunStepEval_encode E state

/-- Any finite encoded run agrees with the structured iteration. -/
theorem scheduledBlockRunStepEval_iterate (E : Nat) (state : ScheduledBlockRunState) (i : Nat) :
    scheduledBlockRunStepEval^[i] (encodeScheduledBlockRun E state) =
      encodeScheduledBlockRun E ((scheduledBlockRunStep E)^[i] state) :=
  Internal.scheduledBlockRunStepEval_iterate E state i

/-- Exact storage cost of the runtime block-state encoding. -/
theorem encodeScheduledBlockRun_length (E : Nat) (state : ScheduledBlockRunState) :
    (encodeScheduledBlockRun E state).length =
      8 * state.dimensions.1 + 4 * state.dimensions.2 + 2 * E + 2 * state.count +
        2 * state.payload.length + state.seeds.length + 18 :=
  Internal.encodeScheduledBlockRun_length E state

/-- The actual loop finishes at the scheduled leaf width and leaf entropy reserve. -/
theorem scheduledBlockRun_dimensions (n h Q E : Nat) (source seeds : List Bool) :
    (scheduledBlockRun n h Q E source seeds).dimensions =
      (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h, Q) :=
  Internal.scheduledBlockRun_dimensions n h Q E source seeds

/-- Each requested level doubles the number of blocks, independently of their contents. -/
theorem scheduledBlockRun_count (n h Q E : Nat) (source seeds : List Bool) :
    (scheduledBlockRun n h Q E source seeds).count = 2 ^ h :=
  Internal.scheduledBlockRun_count n h Q E source seeds

/-- The finite schedule bounds every complete intermediate block-state encoding. -/
theorem scheduledBlockRun_iterate_bound (n h Q E : Nat) (source seeds : List Bool)
    (positive : 0 < Q)
    (budget : 3 * (24 * explicitCondenserBudget (scheduledBlockInitialWidth n h Q E)
      (recursiveBlockEntropy h Q 0) E) + 6 * E ≤ 2 * Q)
    {i : Nat} (level : i ≤ h) :
    (encodeScheduledBlockRun E
      ((scheduledBlockRunStep E)^[i] (scheduledBlockRunInitial n h Q E source seeds))).length ≤
      18 * scheduledBlockInitialWidth n h Q E + 2 * E + seeds.length + 18 :=
  Internal.scheduledBlockRun_iterate_bound n h Q E source seeds positive budget level

open Complexity in
/-- The total encoded step is polynomial-time on every input string. -/
@[polytime] theorem scheduledBlockRunStepEval_mem_FP : scheduledBlockRunStepEval ∈ FP :=
  Internal.scheduledBlockRunStepEval_mem_FP

open Complexity in
/-- One uniform polynomial-time program evaluates the initial condenser and
all internal levels, with an explicit bound throughout the run. -/
theorem scheduledBlockRun_mem_FP {n h Q E : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hn : UnaryFn n)
    (hentropy : UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0)
    (hh : UnaryFn h) (hE : UnaryFn E) (hsource : source ∈ FP) (hseeds : seeds ∈ FP)
    (positive : ∀ z, 0 < Q z)
    (budget : ∀ z, 3 * (24 * explicitCondenserBudget
      (scheduledBlockInitialWidth (n z) (h z) (Q z) (E z))
      (recursiveBlockEntropy (h z) (Q z) 0) (E z)) + 6 * E z ≤ 2 * Q z) :
    (fun z => encodeScheduledBlockRun (E z)
      (scheduledBlockRun (n z) (h z) (Q z) (E z) (source z) (seeds z))) ∈ FP :=
  Internal.scheduledBlockRun_mem_FP hn hentropy hh hE hsource hseeds positive budget

end Algebraic.Cutwidth.Extractor
