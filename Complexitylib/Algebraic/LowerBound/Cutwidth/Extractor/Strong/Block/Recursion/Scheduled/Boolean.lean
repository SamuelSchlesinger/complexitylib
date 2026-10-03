/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Boolean.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Boolean.Internal

/-!
# Strong extraction by the actual Boolean program

The input and uniformly sampled seed are Boolean vectors of their exact
prescribed widths. Output coordinates are read from the actual bit program
in block order. The canonical codec identifies this map with the specified
recursive extractor, and bijective transport preserves its retained-seed
guarantee and source XOR additivity.

The recursive construction and parameter bounds are credited in `Scheduled`.
This layer adds only finite representation transport. Its statements require
no caller-supplied field enumeration instances; those are constructed from
the proved binary quotient cardinalities.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Each actual output bit agrees with the corresponding semantic coordinate at decoded seeds. -/
theorem scheduledBlockBooleanExtractor_eq (n h Q E ell : Nat) (x : Fin n → Bool)
    (seed : Fin (scheduledBlockSeedBits n h Q E ell) → Bool)
    (i : Fin (recursiveBlockCount 1 h)) (j : Fin ell) :
    scheduledBlockBooleanExtractor n h Q E ell x seed i j =
      decide (scheduledBlockExtractor n h Q E ell x
        (decodeScheduledBlockSeeds n h Q E ell (List.ofFn seed)) i j = 1) :=
  Internal.scheduledBlockBooleanExtractor_eq n h Q E ell x seed i j

/-- For any fixed Boolean seed, input XOR becomes pointwise output XOR. -/
theorem scheduledBlockBooleanExtractor_xor (n h Q E ell : Nat) (x x' : Fin n → Bool)
    (seed : Fin (scheduledBlockSeedBits n h Q E ell) → Bool) :
    scheduledBlockBooleanExtractor n h Q E ell (fun i => Bool.xor (x i) (x' i)) seed =
      fun i j => Bool.xor (scheduledBlockBooleanExtractor n h Q E ell x seed i j)
        (scheduledBlockBooleanExtractor n h Q E ell x' seed i j) :=
  Internal.scheduledBlockBooleanExtractor_xor n h Q E ell x x' seed

/-- The actual program is a strong extractor with its full uniformly sampled Boolean seed. -/
theorem scheduledBlockBooleanExtractor_weighted (n h Q E ell : Nat)
    (budget : 3 * (24 * explicitCondenserBudget (scheduledBlockInitialWidth n h Q E)
      (recursiveBlockEntropy h Q 0) E) + 6 * E ≤ 2 * Q)
    (reserve : ell + 2 * E ≤ Q) :
    WeightedStrongSeededExtractor (scheduledBlockBooleanExtractor n h Q E ell)
      (2 ^ recursiveBlockEntropy h Q 0)
      ((3 * (2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ E)⁻¹) :=
  Internal.scheduledBlockBooleanExtractor_weighted n h Q E ell budget reserve

/-- The explicit reserve gives error `2^(-e)` for the actual Boolean-seed program. -/
theorem scheduledBlockBooleanExtractor_dyadic (n h L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    WeightedStrongSeededExtractor
      (scheduledBlockBooleanExtractor n h (recursiveBlockReserve L (e + h + 2)) (e + h + 2) L)
      (2 ^ recursiveBlockEntropy h (recursiveBlockReserve L (e + h + 2)) 0)
      (((2 : ℝ) ^ e)⁻¹) :=
  Internal.scheduledBlockBooleanExtractor_dyadic n h L e length depth

end Algebraic.Cutwidth.Extractor
