/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs

/-!
# A total string evaluator for one affine merging round

The current row supplies a short prefix seed. Extraction from the original
right word gives the middle seed; extraction from the current row gives a
short middle output; extraction from the original right word gives the
final seed; growing-depth extraction from the original left word gives the
next row. Both original source words are reread, without replacing either
by an intermediate output.

This is the four-call round in Chattopadhyay--Liao, *Extractors for Sum of
Two Sources*, Theorem 6.1, <https://arxiv.org/pdf/2110.12652>, using the actual
matched component programs. Statistical guarantees are separate. Every
component remains total on malformed strings and invalid parameters.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Take the common short prefix of the row, completing missing bits by false. -/
def affineRoundPrefixWord (L : Nat) (row : List Bool) : List Bool :=
  (row ++ List.replicate (matchedBlockSeedBits L) false).take (matchedBlockSeedBits L)

/-- Run the four actual component programs while preserving both original source words. -/
def affineRoundRuntime (t L e : Nat) (x y row : List Bool) : List Bool :=
  let middleSeed := matchedBlockExtractorRuntime 24 L e y (affineRoundPrefixWord L row)
  let middleOutput := matchedBlockExtractorRuntime 24 L e row middleSeed
  let finalSeed := matchedBlockExtractorRuntime 24 L e y middleOutput
  growingMatchedBlockExtractorRuntime t L e x finalSeed

/-- Codec: `pair (pair x (pair y row)) (pair parameter (pair scale error))`, unary numbers. -/
def affineRoundEval (z : List Bool) : List Bool :=
  affineRoundRuntime (pairFst (pairSnd z)).length
    (pairFst (pairSnd (pairSnd z))).length (pairSnd (pairSnd (pairSnd z))).length
    (pairFst (pairFst z)) (pairFst (pairSnd (pairFst z))) (pairSnd (pairSnd (pairFst z)))

end Algebraic.Cutwidth.Extractor
