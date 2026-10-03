/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Defs

/-!
# A runtime payload loop for the near-halving schedule

The state stores the actual block width, remaining depth and its power of two,
block count, concatenated payload, and unused seed suffix. Each step consumes
one shared field seed and applies the variable-rate block condenser. The
initial payload is the unchanged source word. A separate iteration count
allows a zero-step run without any splitting budget.

The encoded step is total on arbitrary strings and computes no exponential.
The initializer's power of two must have an explicit uniform unary certificate
when proving polynomial-time iteration. Numerical and complete state-size
bounds are supplied separately; canonical seed semantics is another layer.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Runtime workspace for the near-halving block loop. -/
structure NearHalvingBlockRunState where
  /-- Width of one current block. -/
  width : Nat
  /-- Number of scheduled levels remaining. -/
  remaining : Nat
  /-- Stored power of two of the remaining depth, updated by division. -/
  remainingPower : Nat
  /-- Number of consecutive blocks in the payload. -/
  count : Nat
  /-- Concatenated current block words. -/
  payload : List Bool
  /-- Seed suffix not yet consumed by this run. -/
  seeds : List Bool

/-- Apply the actual shared-seed condenser to every block and advance the workspace. -/
def nearHalvingBlockRunStep (h Q E : Nat) (state : NearHalvingBlockRunState) :
    NearHalvingBlockRunState :=
  let entropy := state.remainingPower * (8 * h + 8 + state.remaining) * Q
  let rate := nearHalvingBlockRate h
  let seedWidth := sparseFieldBits rate (explicitCondenserBudget state.width entropy E)
  { width := explicitCondenserHalfWidth state.width entropy E rate
    remaining := state.remaining - 1
    remainingPower := state.remainingPower / 2
    count := 2 * state.count
    payload := explicitBlockCondenserBits state.width entropy E rate state.payload
      (state.seeds.take seedWidth) (List.replicate state.count true)
    seeds := state.seeds.drop seedWidth }

/-- Encode runtime workspace, static parameters, payload, and unused seed suffix. -/
def encodeNearHalvingBlockRun (h Q E : Nat) (state : NearHalvingBlockRunState) : List Bool :=
  pair
    (pair (pair (List.replicate state.width true) (List.replicate state.remaining true))
      (pair (List.replicate state.remainingPower true) (List.replicate state.count true)))
    (pair (pair (List.replicate h true) (List.replicate Q true))
      (pair (List.replicate E true) (pair state.payload state.seeds)))

/-- One total encoded payload-loop step, with all numeric operands decoded in unary. -/
def nearHalvingBlockRunStepEval (z : List Bool) : List Bool :=
  let dynamic := pairFst z
  let fixed := pairSnd z
  let width := (pairFst (pairFst dynamic)).length
  let remaining := (pairSnd (pairFst dynamic)).length
  let power := (pairFst (pairSnd dynamic)).length
  let count := pairSnd (pairSnd dynamic)
  let h := (pairFst (pairFst fixed)).length
  let Q := (pairSnd (pairFst fixed)).length
  let E := (pairFst (pairSnd fixed)).length
  let payload := pairFst (pairSnd (pairSnd fixed))
  let seeds := pairSnd (pairSnd (pairSnd fixed))
  let entropy := power * (8 * h + 8 + remaining) * Q
  let rate := nearHalvingBlockRate h
  let seedWidth := sparseFieldBits rate (explicitCondenserBudget width entropy E)
  pair
    (pair
      (pair (List.replicate (explicitCondenserHalfWidth width entropy E rate) true)
        (List.replicate (remaining - 1) true))
      (pair (List.replicate (power / 2) true) (List.replicate (2 * count.length) true)))
    (pair (pair (List.replicate h true) (List.replicate Q true))
      (pair (List.replicate E true)
        (pair (explicitBlockCondenserBits width entropy E rate payload
            (seeds.take seedWidth) count)
          (seeds.drop seedWidth))))

/-- Identity initialization keeps the source and every seed bit unchanged. -/
def nearHalvingBlockRunInitial (N h : Nat) (source seeds : List Bool) :
    NearHalvingBlockRunState :=
  { width := N
    remaining := h
    remainingPower := 2 ^ h
    count := 1
    payload := source
    seeds := seeds }

/-- Execute any requested number of payload steps from the identity initialization. -/
def nearHalvingBlockRun (N h Q E count : Nat) (source seeds : List Bool) :
    NearHalvingBlockRunState :=
  (nearHalvingBlockRunStep h Q E)^[count] (nearHalvingBlockRunInitial N h source seeds)

end Algebraic.Cutwidth.Extractor
