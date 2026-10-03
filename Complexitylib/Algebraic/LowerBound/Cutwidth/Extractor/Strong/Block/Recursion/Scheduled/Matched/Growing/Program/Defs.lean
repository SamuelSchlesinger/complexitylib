/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs

/-!
# A total matched-extractor runtime at logarithmic depth

The unary parameter `t` selects depth `clog 2 (t+1) + 64`. Thus the leaf
count is polynomial in `t`, even though the permitted depth is unbounded.
The finite growing-depth guard ensures the schedule fits the supplied
scale and padded seed width. Invalid parameters return the empty word.

The paired evaluator stores source and seed words together, followed by
unary words for `t`, the scale, and the requested error exponent. All pair
projections are total, including on malformed strings. The valid branch
uses exactly the required seed prefix of the existing scheduled program.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Logarithmic recursion depth with the fixed reserve used by the affine construction. -/
def growingMatchedBlockDepth (t : Nat) : Nat := Nat.clog 2 (t + 1) + 64

/-- Finite conditions for growing-depth extraction at the supplied common scale. -/
def GrowingMatchedBlockRuntimeValid (n t L e : Nat) : Prop :=
  let h := growingMatchedBlockDepth t
  Nat.clog 2 (n + 1) ≤ L ∧ e + h + 2 ≤ L ∧
    (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L

/-- The guard uses only natural arithmetic and ceiling logarithms. -/
instance (n t L e : Nat) : Decidable (GrowingMatchedBlockRuntimeValid n t L e) :=
  inferInstanceAs (Decidable (Nat.clog 2 (n + 1) ≤ L ∧
    e + growingMatchedBlockDepth t + 2 ≤ L ∧
    (growingMatchedBlockDepth t + 1) *
      (e + 2 * growingMatchedBlockDepth t + Nat.clog 2 (L + 1) + 4) ≤ L))

/-- Run the existing bit program at logarithmic depth, discarding unused seed padding. -/
def growingMatchedBlockExtractorRuntime (t L e : Nat) (source seeds : List Bool) : List Bool :=
  if GrowingMatchedBlockRuntimeValid source.length t L e then
    let h := growingMatchedBlockDepth t
    let E := e + h + 2
    let Q := recursiveBlockReserve L E
    scheduledBlockExtractorBits source.length h Q E L source
      (seeds.take (scheduledBlockSeedBits source.length h Q E L))
  else []

/-- Codec: `pair (pair source seeds) (pair parameter (pair scale error))`, with unary numbers. -/
def growingMatchedBlockExtractorEval (z : List Bool) : List Bool :=
  growingMatchedBlockExtractorRuntime (pairFst (pairSnd z)).length
    (pairFst (pairSnd (pairSnd z))).length (pairSnd (pairSnd (pairSnd z))).length
    (pairFst (pairFst z)) (pairSnd (pairFst z))

end Algebraic.Cutwidth.Extractor
