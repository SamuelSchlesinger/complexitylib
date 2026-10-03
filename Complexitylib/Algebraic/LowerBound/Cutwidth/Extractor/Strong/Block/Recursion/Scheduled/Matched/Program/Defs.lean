/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs

/-!
# A total runtime for a scheduled extractor with a shared scale

The surrounding protocol supplies the common scale `L`. Valid parameters
use the existing complete scheduled program, after cutting the seed word
to the exact schedule width. This cut prevents unused padding from entering
the final field hash. Invalid parameters return the empty word before any
depth-dependent schedule is evaluated.

The paired interface stores source and seed words together and uses word
lengths for the three numerical inputs. Decoding remains total on malformed
pairings. The runtime does not enumerate semantic field elements.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Finite conditions permitting the shared-scale schedule and its fixed padded seed budget. -/
def MatchedBlockRuntimeValid (n h L e : Nat) : Prop :=
  64 ≤ L ∧ h ≤ 64 ∧ e + h + 2 ≤ L ∧ Nat.clog 2 (n + 1) ≤ L

/-- The runtime guard is decided by natural-number comparisons and a ceiling logarithm. -/
instance (n h L e : Nat) : Decidable (MatchedBlockRuntimeValid n h L e) :=
  inferInstanceAs (Decidable (64 ≤ L ∧ h ≤ 64 ∧ e + h + 2 ≤ L ∧
    Nat.clog 2 (n + 1) ≤ L))

/-- Run the actual scheduled extractor at a common supplied scale, ignoring unused seed padding. -/
def matchedBlockExtractorRuntime (h L e : Nat) (source seeds : List Bool) : List Bool :=
  if MatchedBlockRuntimeValid source.length h L e then
    let E := e + h + 2
    let Q := recursiveBlockReserve L E
    scheduledBlockExtractorBits source.length h Q E L source
      (seeds.take (scheduledBlockSeedBits source.length h Q E L))
  else []

/-- Codec: `pair (pair source seeds) (pair depth (pair scale error))`, with unary numbers. -/
def matchedBlockExtractorEval (z : List Bool) : List Bool :=
  matchedBlockExtractorRuntime (pairFst (pairSnd z)).length
    (pairFst (pairSnd (pairSnd z))).length (pairSnd (pairSnd (pairSnd z))).length
    (pairFst (pairFst z)) (pairSnd (pairFst z))

end Algebraic.Cutwidth.Extractor
