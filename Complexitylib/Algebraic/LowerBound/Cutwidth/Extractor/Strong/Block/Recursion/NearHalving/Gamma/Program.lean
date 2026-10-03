/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Internal

/-!
# A uniform total program for the rounded Gamma family

The runtime generates the rounded parameters, executes the certified number
of near-halving levels, and returns exactly the requested output width.
It is polynomial-time on all source and seed words, including inputs outside
the statistical size guard. The paired evaluator infers the target width as
the decoded source length divided by eight.

These are program and resource statements. Agreement with the semantic
extractor on canonical seeds is proved in the correctness layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- On the size guard, run the selected depth and retain the requested output prefix. -/
theorem gammaBlockExtractorRuntime_of_guard (b : Nat) (source seeds : List Bool)
    (guard : GammaBlockSizeGuard b) :
    gammaBlockExtractorRuntime b source seeds =
      (nearHalvingBlockExtractorBits (8 * b) (gammaBlockDepth b) (gammaBlockReserve b)
        (gammaBlockErrorExponent b) (gammaBlockLeafLength b) (gammaBlockDepth b)
        source seeds).take b :=
  Internal.gammaBlockExtractorRuntime_of_guard b source seeds guard

/-- Outside the size guard, the total runtime emits an all-false word. -/
theorem gammaBlockExtractorRuntime_of_not_guard (b : Nat) (source seeds : List Bool)
    (guard : ¬ GammaBlockSizeGuard b) :
    gammaBlockExtractorRuntime b source seeds = List.replicate b false :=
  Internal.gammaBlockExtractorRuntime_of_not_guard b source seeds guard

/-- Every source and seed word yields exactly the requested number of output bits. -/
theorem gammaBlockExtractorRuntime_length (b : Nat) (source seeds : List Bool) :
    (gammaBlockExtractorRuntime b source seeds).length = b :=
  Internal.gammaBlockExtractorRuntime_length b source seeds

open Complexity in
/-- The paired evaluator decodes its source and seed words before inferring the width. -/
theorem gammaBlockExtractorEval_pair (source seeds : List Bool) :
    gammaBlockExtractorEval (pair source seeds) =
      gammaBlockExtractorRuntime (source.length / 8) source seeds :=
  Internal.gammaBlockExtractorEval_pair source seeds

open Complexity in
/-- Arbitrary encoded words have the output width determined by their decoded source. -/
theorem gammaBlockExtractorEval_length (z : List Bool) :
    (gammaBlockExtractorEval z).length = (pairFst z).length / 8 :=
  Internal.gammaBlockExtractorEval_length z

open Complexity in
/-- The total runtime is polynomial-time in its unary width and two runtime words. -/
@[polytime] theorem gammaBlockExtractorRuntime_mem_FP {b : List Bool → Nat}
    {source seeds : List Bool → List Bool} (hb : UnaryFn b)
    (hsource : source ∈ FP) (hseeds : seeds ∈ FP) :
    (fun z => gammaBlockExtractorRuntime (b z) (source z) (seeds z)) ∈ FP :=
  Internal.gammaBlockExtractorRuntime_mem_FP hb hsource hseeds

open Complexity in
/-- One polynomial-time program evaluates the family on every encoded input word. -/
@[polytime] theorem gammaBlockExtractorEval_mem_FP : gammaBlockExtractorEval ∈ FP :=
  Internal.gammaBlockExtractorEval_mem_FP

end Algebraic.Cutwidth.Extractor
