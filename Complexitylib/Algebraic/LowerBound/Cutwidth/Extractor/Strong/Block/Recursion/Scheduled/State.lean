/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Internal

/-!
# Uniform bounded evaluation of the numerical block schedule

The two-component numerical transition agrees with the prescribed width
and entropy through the scheduled depth. Its string evaluator has one
uniform polynomial-time certificate. Complete iteration additionally bounds
every state, including the fixed error workspace; the proved schedule bounds
supply a width of `6*initial+E+6` bits.

These are arithmetic and machine consequences for the finite recursive
program. Its probabilistic source credits are in `Recursion.Extraction`.
The statements here compute numerical parameters; evaluating the block
payload and consuming its seeds are separate constructions.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Division by four tracks the prescribed entropy at every executed level. -/
theorem scheduledBlockStateStep_iterate (initial h Q E : Nat) {i : Nat} (level : i ≤ h) :
    (scheduledBlockStateStep E)^[i] (initial, recursiveBlockEntropy h Q 0) =
      (recursiveBlockWidth initial h Q E i, recursiveBlockEntropy h Q i) :=
  Internal.scheduledBlockStateStep_iterate initial h Q E level

/-- The total string step computes the numerical transition on encoded states. -/
theorem scheduledBlockStateStepEval_encode (E : Nat) (state : Nat × Nat) :
    scheduledBlockStateStepEval (encodeScheduledBlockState E state) =
      encodeScheduledBlockState E (scheduledBlockStateStep E state) :=
  Internal.scheduledBlockStateStepEval_encode E state

/-- Repeated string steps compute the exact numerical iterate. -/
theorem scheduledBlockStateStepEval_iterate (E : Nat) (state : Nat × Nat) (i : Nat) :
    scheduledBlockStateStepEval^[i] (encodeScheduledBlockState E state) =
      encodeScheduledBlockState E ((scheduledBlockStateStep E)^[i] state) :=
  Internal.scheduledBlockStateStepEval_iterate E state i

/-- Exact unary state width, including both pairing separators and fixed workspace. -/
theorem encodeScheduledBlockState_length (E : Nat) (state : Nat × Nat) :
    (encodeScheduledBlockState E state).length = 4 * state.1 + 2 * state.2 + E + 6 :=
  Internal.encodeScheduledBlockState_length E state

/-- One numerical state transition is uniformly polynomial-time on every input word. -/
@[polytime] theorem scheduledBlockStateStepEval_mem_FP : scheduledBlockStateStepEval ∈ FP :=
  Internal.scheduledBlockStateStepEval_mem_FP

/-- Complete numerical iteration is polynomial-time under a bound on every intermediate state. -/
theorem scheduledBlockState_iterate_mem_FP {initial entropy E count B : List Bool → Nat}
    (hinitial : UnaryFn initial) (hentropy : UnaryFn entropy) (hE : UnaryFn E)
    (hcount : UnaryFn count) (hB : UnaryFn B)
    (bounded : ∀ z j, j ≤ count z →
      ((scheduledBlockStateStep (E z))^[j] (initial z, entropy z)).1 ≤ B z ∧
        ((scheduledBlockStateStep (E z))^[j] (initial z, entropy z)).2 ≤ B z) :
    (fun z => encodeScheduledBlockState (E z)
      ((scheduledBlockStateStep (E z))^[count z] (initial z, entropy z))) ∈ FP :=
  Internal.scheduledBlockState_iterate_mem_FP hinitial hentropy hE hcount hB bounded

/-- The global reserve and capacity bounds certify every intermediate scheduled state. -/
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
        recursiveBlockEntropy (h z) (Q z) (count z))) ∈ FP :=
  Internal.scheduledBlockState_mem_FP hinitial hentropy hE hcount capacity budget levels

/-- A certified capacity bound permits uniform unary generation of the initial entropy.
The bounded-power computation also handles a zero leaf reserve. -/
theorem recursiveBlockEntropy_zero_unaryFn {initial h Q : List Bool → Nat}
    (hinitial : UnaryFn initial) (hh : UnaryFn h) (hQ : UnaryFn Q)
    (capacity : ∀ z, recursiveBlockEntropy (h z) (Q z) 0 ≤ initial z) :
    UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0 :=
  Internal.recursiveBlockEntropy_zero_unaryFn hinitial hh hQ capacity

end Algebraic.Cutwidth.Extractor
