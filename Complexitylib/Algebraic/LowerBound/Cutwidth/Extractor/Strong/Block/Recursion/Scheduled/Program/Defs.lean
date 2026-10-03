/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.State.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program.Defs

/-!
# The complete scheduled extractor as a bit program

Run the initial condenser and the internal block loop, then use the final
two shared field seeds for one-shot extraction on every leaf. The complete
seed word is consumed in stage order without copying any seed per block.

The total runtime wrapper derives the source length, clips the requested
depth to its ceiling logarithm, and generates the error and entropy
parameters. Its paired interface accepts only source, seed word, requested
depth, and requested error exponent; all numerical parameters are generated
by the same program.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Finish every leaf using the final pair of shared field seeds. -/
def scheduledBlockFinish (E ell : Nat) (state : ScheduledBlockRunState) : List Bool :=
  let width := state.dimensions.1
  let seedWidth := 2 * 3 ^ oneShotCondenserExponent width ell E
  oneShotBlockExtractorBits width ell E state.payload
    (state.seeds.take seedWidth) (state.seeds.drop seedWidth) (List.replicate state.count true)

/-- Decode an encoded runtime state and unary output length, then extract every leaf. -/
def scheduledBlockFinishEval (z : List Bool) : List Bool :=
  let state := pairFst z
  let ell := (pairSnd z).length
  let scalar := pairFst state
  let data := pairSnd state
  let width := (pairFst (pairFst scalar)).length
  let E := (pairSnd scalar).length
  let count := pairFst data
  let payload := pairFst (pairSnd data)
  let seeds := pairSnd (pairSnd data)
  let seedWidth := 2 * 3 ^ oneShotCondenserExponent width ell E
  oneShotBlockExtractorBits width ell E payload
    (seeds.take seedWidth) (seeds.drop seedWidth) count

/-- Evaluate the specified extractor using one flat seed word. -/
def scheduledBlockExtractorBits (n h Q E ell : Nat) (source seeds : List Bool) : List Bool :=
  scheduledBlockFinish E ell (scheduledBlockRun n h Q E source seeds)

/-- Generate a valid finite schedule from the source length and the requested depth and error. -/
def scheduledBlockExtractorRuntime (requested e : Nat) (source seeds : List Bool) : List Bool :=
  let n := source.length
  scheduledBlockExtractorBits n (scheduledBlockDepth n requested)
    (scheduledBlockLeafReserve n requested e) (scheduledBlockErrorExponent n requested e)
    (scheduledBlockInputLog n) source seeds

/-- Codec: `pair (pair source seeds) (pair unaryRequestedDepth unaryError)`. -/
def scheduledBlockExtractorEval (z : List Bool) : List Bool :=
  scheduledBlockExtractorRuntime (pairFst (pairSnd z)).length (pairSnd (pairSnd z)).length
    (pairFst (pairFst z)) (pairSnd (pairFst z))

end Algebraic.Cutwidth.Extractor
