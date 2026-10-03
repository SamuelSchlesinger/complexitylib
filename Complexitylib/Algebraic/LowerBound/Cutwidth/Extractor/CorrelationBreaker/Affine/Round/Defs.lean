/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs

/-!
# The actual extraction round in the affine construction

Starting with a previous long row, the round extracts from the original
right source using the row prefix, extracts a short row using that seed,
extracts again from the same original right source, and finally extracts
the next long row from the original left input. All four calls are actual
matched extractors. Short seeds and outputs share the depth-twenty-four
width; the long-row depth is an arbitrary semantic parameter.

This is the second-phase round in Chattopadhyay--Liao, *Extractors for Sum
of Two Sources* (2021), proof of Theorem 6.1, printed pp.23--25:
<https://arxiv.org/abs/2110.12652>. The total prefix uses false completion.
No numerical guard or statistical assertion is built into these definitions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The previous row's seed-width prefix, completed with false bits when necessary. -/
def affineRoundPrefix (h L : Nat) (row : Fin (matchedBlockOutputBits h L) → Bool) :
    Fin (matchedBlockSeedBits L) → Bool :=
  fun i => (List.ofFn row)[i.val]?.getD false

/-- The first right-source call uses the prefix of the actual previous row. -/
def affineRoundMiddleSeed (d h L e : Nat) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits h L) → Bool) : Fin (matchedBlockSeedBits L) → Bool :=
  matchedBlockExtractor d 24 L e y (affineRoundPrefix h L row)

/-- The short linear extraction rereads the actual previous long row. -/
def affineRoundMiddleOutput (d h L e : Nat) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits h L) → Bool) : Fin (matchedBlockSeedBits L) → Bool :=
  matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e row
    (affineRoundMiddleSeed d h L e y row)

/-- The second right-source call rereads the original right word. -/
def affineRoundFinalSeed (d h L e : Nat) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits h L) → Bool) : Fin (matchedBlockSeedBits L) → Bool :=
  matchedBlockExtractor d 24 L e y (affineRoundMiddleOutput d h L e y row)

/-- The next long row is extracted from the original left input with the actual final seed. -/
def affineRoundOutput (n d h L e : Nat) (x : Fin n → Bool) (y : Fin d → Bool)
    (row : Fin (matchedBlockOutputBits h L) → Bool) : Fin (matchedBlockOutputBits h L) → Bool :=
  matchedBlockExtractor n h L e x (affineRoundFinalSeed d h L e y row)

end Algebraic.Cutwidth.Extractor
