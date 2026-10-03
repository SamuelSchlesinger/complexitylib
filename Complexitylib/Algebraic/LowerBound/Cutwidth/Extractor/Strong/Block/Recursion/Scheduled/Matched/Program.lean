/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program.Internal

/-!
# Uniform runtime for the matched-width scheduled extractor

The protocol's supplied scale determines both leaf output width and reserve.
The checked guard bounds the depth before any variable power is generated;
the complete numerical, seed-width, and payload computations have one uniform
FP certificate. Invalid parameters give an empty output. Valid parameters
run the existing scheduled bit program with exactly its required seed prefix.
At canonical Boolean words the runtime equals `matchedBlockExtractor`,
including when an arbitrary extra seed suffix is supplied.

This is an evaluator for the actual construction. Its statistical guarantee
and seed budget are supplied by `Scheduled.Matched`; no semantic field
enumeration or caller-supplied numerical resource premise occurs here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Valid inputs run the prescribed schedule after discarding unused seed padding. -/
theorem matchedBlockExtractorRuntime_of_valid (h L e : Nat) (source seeds : List Bool)
    (valid : MatchedBlockRuntimeValid source.length h L e) :
    matchedBlockExtractorRuntime h L e source seeds =
      scheduledBlockExtractorBits source.length h (recursiveBlockReserve L (e + h + 2))
        (e + h + 2) L source (seeds.take (scheduledBlockSeedBits source.length h
          (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)) :=
  Internal.matchedBlockExtractorRuntime_of_valid h L e source seeds valid

/-- Invalid parameters return the empty word. -/
theorem matchedBlockExtractorRuntime_of_not_valid (h L e : Nat) (source seeds : List Bool)
    (invalid : ¬ MatchedBlockRuntimeValid source.length h L e) :
    matchedBlockExtractorRuntime h L e source seeds = [] :=
  Internal.matchedBlockExtractorRuntime_of_not_valid h L e source seeds invalid

/-- The accepted schedule outputs one `L`-bit word per leaf. -/
theorem matchedBlockExtractorRuntime_length (h L e : Nat) (source seeds : List Bool) :
    (matchedBlockExtractorRuntime h L e source seeds).length =
      if MatchedBlockRuntimeValid source.length h L e then 2 ^ h * L else 0 :=
  Internal.matchedBlockExtractorRuntime_length h L e source seeds

/-- The output width is bounded for every supplied depth, including invalid inputs. -/
theorem matchedBlockExtractorRuntime_length_le (h L e : Nat) (source seeds : List Bool) :
    (matchedBlockExtractorRuntime h L e source seeds).length ≤ 2 ^ 64 * L :=
  Internal.matchedBlockExtractorRuntime_length_le h L e source seeds

open Complexity in
/-- The validity guard is uniformly polynomial-time in its unary parameters. -/
@[polytime] theorem matchedBlockRuntimeValid_fpPred {n h L e : List Bool → Nat}
    (hn : UnaryFn n) (hh : UnaryFn h) (hL : UnaryFn L) (he : UnaryFn e) :
    FPPred fun z => MatchedBlockRuntimeValid (n z) (h z) (L z) (e z) :=
  Internal.matchedBlockRuntimeValid_fpPred hn hh hL he

open Complexity in
/-- Complete shared-scale extraction is uniformly polynomial-time on arbitrary runtime inputs. -/
@[polytime] theorem matchedBlockExtractorRuntime_mem_FP {h L e : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hh : UnaryFn h) (hL : UnaryFn L) (he : UnaryFn e)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => matchedBlockExtractorRuntime (h z) (L z) (e z) (source z) (seeds z)) ∈ FP :=
  Internal.matchedBlockExtractorRuntime_mem_FP hh hL he hsource hseeds

open Complexity in
/-- The paired interface reads source and seed words and three unary numerical parameters. -/
theorem matchedBlockExtractorEval_pair (source seeds depth scale error : List Bool) :
    matchedBlockExtractorEval (pair (pair source seeds) (pair depth (pair scale error))) =
      matchedBlockExtractorRuntime depth.length scale.length error.length source seeds :=
  Internal.matchedBlockExtractorEval_pair source seeds depth scale error

open Complexity in
/-- One total paired string evaluator includes all parameter and payload computations. -/
@[polytime] theorem matchedBlockExtractorEval_mem_FP : matchedBlockExtractorEval ∈ FP :=
  Internal.matchedBlockExtractorEval_mem_FP

/-- On canonical words, the runtime computes exactly the actual matched Boolean extractor. -/
theorem matchedBlockExtractorRuntime_eq_matchedBlockExtractor (n h L e : Nat)
    (valid : MatchedBlockRuntimeValid n h L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) :
    matchedBlockExtractorRuntime h L e (List.ofFn x) (List.ofFn seed) =
      List.ofFn (matchedBlockExtractor n h L e x seed) :=
  Internal.matchedBlockExtractorRuntime_eq_matchedBlockExtractor n h L e valid x seed

/-- Extra seed padding is ignored, preserving exact agreement with the Boolean extractor. -/
theorem matchedBlockExtractorRuntime_append_eq_matchedBlockExtractor (n h L e : Nat)
    (valid : MatchedBlockRuntimeValid n h L e) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) (tail : List Bool) :
    matchedBlockExtractorRuntime h L e (List.ofFn x) (List.ofFn seed ++ tail) =
      List.ofFn (matchedBlockExtractor n h L e x seed) :=
  Internal.matchedBlockExtractorRuntime_append_eq_matchedBlockExtractor n h L e valid x seed tail

end Algebraic.Cutwidth.Extractor
