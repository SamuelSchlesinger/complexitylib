/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Defs

/-!
# Runtime block payloads and seed consumption

Each state stores the current width and entropy, the block count, the
concatenated block payload, and the unused seed suffix. One step uses the
next field-width prefix as the shared condenser seed, splits every output
into its consecutive halves, and discards exactly that seed prefix.

The numerical error exponent is fixed workspace in the string encoding.
All programs are total, including on short seed words or malformed pairing
encodings. Agreement with the statistical map uses canonical seed words;
polynomial-time iteration additionally needs the proved state-size bounds.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Runtime data at a level of the scheduled block recursion. -/
structure ScheduledBlockRunState where
  /-- Current block width and entropy threshold, in bits. -/
  dimensions : Nat × Nat
  /-- Number of consecutive equal-width blocks. -/
  count : Nat
  /-- Concatenation of the current block words. -/
  payload : List Bool
  /-- Seed bits not yet consumed by an earlier stage. -/
  seeds : List Bool

/-- Condense every block using one fresh seed prefix, then advance the state. -/
def scheduledBlockRunStep (E : Nat) (state : ScheduledBlockRunState) :
    ScheduledBlockRunState :=
  let width := state.dimensions.1
  let entropy := state.dimensions.2
  let seedWidth := sparseFieldBits 3 (explicitCondenserBudget width entropy E)
  { dimensions := scheduledBlockStateStep E state.dimensions
    count := 2 * state.count
    payload := explicitBlockCondenserBits width entropy E 3 state.payload
      (state.seeds.take seedWidth) (List.replicate state.count true)
    seeds := state.seeds.drop seedWidth }

/-- Encode numerical workspace, block count, payload, and unused seed suffix. -/
def encodeScheduledBlockRun (E : Nat) (state : ScheduledBlockRunState) : List Bool :=
  pair (encodeScheduledBlockState E state.dimensions)
    (pair (List.replicate state.count true) (pair state.payload state.seeds))

/-- One total step of the runtime payload loop on paired bit strings. -/
def scheduledBlockRunStepEval (z : List Bool) : List Bool :=
  let scalar := pairFst z
  let data := pairSnd z
  let width := (pairFst (pairFst scalar)).length
  let entropy := (pairSnd (pairFst scalar)).length
  let E := (pairSnd scalar).length
  let count := pairFst data
  let payload := pairFst (pairSnd data)
  let seeds := pairSnd (pairSnd data)
  let seedWidth := sparseFieldBits 3 (explicitCondenserBudget width entropy E)
  pair (scheduledBlockStateStepEval scalar)
    (pair (List.replicate (2 * count.length) true)
      (pair (explicitBlockCondenserBits width entropy E 3 payload
          (seeds.take seedWidth) count)
        (seeds.drop seedWidth)))

/-- The initial condenser consumes the first seed and produces one compressed block. -/
def scheduledBlockRunInitial (n h Q E : Nat) (source seeds : List Bool) :
    ScheduledBlockRunState :=
  let entropy := recursiveBlockEntropy h Q 0
  let seedWidth := sparseFieldBits 1 (explicitCondenserBudget n entropy E)
  { dimensions := (scheduledBlockInitialWidth n h Q E, entropy)
    count := 1
    payload := explicitCondenserBits n entropy E 1 source (seeds.take seedWidth)
    seeds := seeds.drop seedWidth }

/-- Run the actual initial condenser and all requested internal block levels. -/
def scheduledBlockRun (n h Q E : Nat) (source seeds : List Bool) : ScheduledBlockRunState :=
  (scheduledBlockRunStep E)^[h] (scheduledBlockRunInitial n h Q E source seeds)

end Algebraic.Cutwidth.Extractor
