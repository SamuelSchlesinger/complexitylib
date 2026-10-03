/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit.Defs

/-!
# A total runtime for the rounded Gamma parameters

All numerical parameters come from the target width. The block loop executes
the selected depth when the size guard holds and zero steps otherwise. The
runtime returns the requested output prefix on the guarded branch, and an
all-false word of the same width on the other branch.

The paired evaluator infers its target width as the source-word length
divided by eight. Pair decoding and source lengths not divisible by eight
remain total. Statistical correctness on canonical words is a separate layer.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- The runtime decides its size guard by the explicit inequality of natural logarithms. -/
local instance (b : Nat) : Decidable (GammaBlockSizeGuard b) :=
  inferInstanceAs (Decidable (3 * Nat.clog 2 (gammaBlockLog b + 1) + 15 ≤ Nat.log 2 b))

/-- Generate all parameters, run only the guarded number of levels, and emit exactly `b` bits. -/
def gammaBlockExtractorRuntime (b : Nat) (source seeds : List Bool) : List Bool :=
  let depth := gammaBlockDepth b
  let count := if GammaBlockSizeGuard b then depth else 0
  let output := nearHalvingBlockExtractorBits (8 * b) depth (gammaBlockReserve b)
    (gammaBlockErrorExponent b) (gammaBlockLeafLength b) count source seeds
  if GammaBlockSizeGuard b then output.take b else List.replicate b false

/-- Codec: `pair source seeds`; the target width is the source length divided by eight. -/
def gammaBlockExtractorEval (z : List Bool) : List Bool :=
  let source := pairFst z
  gammaBlockExtractorRuntime (source.length / 8) source (pairSnd z)

end Algebraic.Cutwidth.Extractor
