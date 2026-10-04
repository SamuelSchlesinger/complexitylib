/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Defs

/-!
# The total amplified-sampler program

Gamma reads the outer and candidate words and produces the seed for the
growing-depth matched program on the original source word. Take the desired
output prefix, completing it by false bits. Both component programs retain
their total behavior on malformed inputs and invalid parameter choices.
The paired evaluator reads three words and two unary widths.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Run both actual component programs and produce exactly `d` output bits. -/
def amplifiedMatchedSamplerRuntime (L d : Nat) (source outer candidate : List Bool) : List Bool :=
  let seed := gammaBlockExtractorRuntime (matchedBlockSeedBits L) outer candidate
  let output := growingMatchedBlockExtractorRuntime d L 4 source seed
  (output ++ List.replicate d false).take d

/-- Codec: `pair (pair source (pair outer candidate)) (pair scale outputWidth)`, unary widths. -/
def amplifiedMatchedSamplerEval (z : List Bool) : List Bool :=
  amplifiedMatchedSamplerRuntime (pairFst (pairSnd z)).length (pairSnd (pairSnd z)).length
    (pairFst (pairFst z)) (pairFst (pairSnd (pairFst z))) (pairSnd (pairSnd (pairFst z)))

end Algebraic.Cutwidth.Extractor
