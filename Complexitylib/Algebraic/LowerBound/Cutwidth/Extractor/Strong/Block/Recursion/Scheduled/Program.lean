/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Internal

/-!
# A uniform polynomial-time program for the complete recursive extractor

One program generates the actual rounded parameters, runs initial
condensation and every internal block level, and extracts all leaves with
one final shared seed pair. The requested depth is clipped to the ceiling
binary logarithm of the source length, so every input has a valid reserve
budget and polynomial bounds on the complete run. A valid requested depth
is unchanged by this clipping.

The public evaluator accepts paired source, seed word, unary requested
depth, and unary error exponent. Its FP theorem has no numerical validity
premise and covers malformed pairing inputs through the total projections.
Canonical seed words connect this program to the statistical map in the
separate correctness layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The full bit program emits the requested number of leaf output bits. -/
theorem scheduledBlockExtractorBits_length (n h Q E ell : Nat) (source seeds : List Bool) :
    (scheduledBlockExtractorBits n h Q E ell source seeds).length = 2 ^ h * ell :=
  Internal.scheduledBlockExtractorBits_length n h Q E ell source seeds

open Complexity in
/-- The specified bit program is uniform in all unary parameters under the global reserve budget. -/
theorem scheduledBlockExtractorBits_mem_FP {n h Q E ell : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hn : UnaryFn n)
    (hentropy : UnaryFn fun z => recursiveBlockEntropy (h z) (Q z) 0)
    (hh : UnaryFn h) (hE : UnaryFn E) (hell : UnaryFn ell)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) (positive : ∀ z, 0 < Q z)
    (budget : ∀ z, 3 * (24 * explicitCondenserBudget
      (scheduledBlockInitialWidth (n z) (h z) (Q z) (E z))
      (recursiveBlockEntropy (h z) (Q z) 0) (E z)) + 6 * E z ≤ 2 * Q z) :
    (fun z => scheduledBlockExtractorBits (n z) (h z) (Q z) (E z) (ell z)
      (source z) (seeds z)) ∈ FP :=
  Internal.scheduledBlockExtractorBits_mem_FP hn hentropy hh hE hell hsource hseeds positive budget

open Complexity in
/-- Parameter generation and complete extraction form one uniform polynomial-time map. -/
@[polytime] theorem scheduledBlockExtractorRuntime_mem_FP {requested e : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hrequested : UnaryFn requested) (he : UnaryFn e)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => scheduledBlockExtractorRuntime (requested z) (e z) (source z) (seeds z)) ∈ FP :=
  Internal.scheduledBlockExtractorRuntime_mem_FP hrequested he hsource hseeds

open Complexity in
/-- The paired evaluator decodes the source, flat seed word, requested depth, and error. -/
theorem scheduledBlockExtractorEval_pair (source seeds requested error : List Bool) :
    scheduledBlockExtractorEval (pair (pair source seeds) (pair requested error)) =
      scheduledBlockExtractorRuntime requested.length error.length source seeds :=
  Internal.scheduledBlockExtractorEval_pair source seeds requested error

/-- A requested depth within the logarithmic budget is evaluated without alteration. -/
theorem scheduledBlockExtractorRuntime_of_depth_le (requested e : Nat)
    (source seeds : List Bool) (depth : requested ≤ Nat.clog 2 (source.length + 1)) :
    scheduledBlockExtractorRuntime requested e source seeds =
      scheduledBlockExtractorBits source.length requested
        (recursiveBlockReserve (Nat.clog 2 (source.length + 1)) (e + requested + 2))
        (e + requested + 2) (Nat.clog 2 (source.length + 1)) source seeds :=
  Internal.scheduledBlockExtractorRuntime_of_depth_le requested e source seeds depth

open Complexity in
/-- The single total paired evaluator is polynomial-time on every input word. -/
@[polytime] theorem scheduledBlockExtractorEval_mem_FP : scheduledBlockExtractorEval ∈ FP :=
  Internal.scheduledBlockExtractorEval_mem_FP

end Algebraic.Cutwidth.Extractor
