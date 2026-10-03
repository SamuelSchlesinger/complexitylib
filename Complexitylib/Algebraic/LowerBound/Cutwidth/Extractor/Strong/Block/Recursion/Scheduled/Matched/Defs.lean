/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs

/-!
# Matched Boolean seed and output widths for the scheduled extractor

The source and the padded seed are Boolean vectors. The actual scheduled
bit program receives precisely its prescribed seed prefix, with `false`
completion if the supplied budget is too small. Its output is read in flat
block order. Thus every parameter choice has a total deterministic meaning,
including zero widths; statistical guarantees use separate finite bounds.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The common padded seed width for recursion depths at most sixty-four. -/
def matchedBlockSeedBits (L : Nat) : Nat := 2 ^ 24 * L

/-- The exact flattened output width at the chosen recursion depth. -/
def matchedBlockOutputBits (h L : Nat) : Nat := 2 ^ h * L

/-- Run the actual scheduled program at the common seed and output widths. -/
def matchedBlockExtractor (n h L e : Nat) (x : Fin n → Bool)
    (seed : Fin (matchedBlockSeedBits L) → Bool) (j : Fin (matchedBlockOutputBits h L)) : Bool :=
  let Q := recursiveBlockReserve L (e + h + 2)
  let exactSeed : Fin (scheduledBlockSeedBits n h Q (e + h + 2) L) → Bool :=
    fun i => (List.ofFn seed)[i.val]?.getD false
  let output := scheduledBlockExtractorBits n h Q (e + h + 2) L
    (List.ofFn x) (List.ofFn exactSeed)
  output[j.val]?.getD false

end Algebraic.Cutwidth.Extractor
