/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Seeds.Internal

/-!
# The exact finite seed size of the scheduled extractor

The actual initial, recursive, and final field seed tuple has cardinality
`2^scheduledBlockSeedBits`. With the explicit leaf reserve, the number of
seed bits is bounded by a concrete expression in the input logarithm,
recursion depth, and error exponent. Every seed is counted once, including
the final pair shared by all leaves.

These are finite counting and arithmetic bounds. They do not assert an
asymptotic parameter choice or a uniform evaluator for the full recursion.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The complete retained seed tuple has exactly the stated power-of-two cardinality. -/
theorem card_scheduledBlockSeeds (n h Q E ell : Nat)
    [∀ s, Fintype (AdjoinRoot (binaryModulus s))] :
    Fintype.card (RecursiveSeeds (ScheduledInitialSeed n h Q E)
      (ScheduledLevelSeed n h Q E) h × ScheduledFinalSeed n h Q E ell) =
      2 ^ scheduledBlockSeedBits n h Q E ell :=
  Internal.card_scheduledBlockSeeds n h Q E ell

/-- A concrete seed-bit bound for the explicit reserve and `L` output bits per leaf. -/
theorem scheduledBlockSeedBits_le (n L E h : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (depth : h ≤ L) :
    scheduledBlockSeedBits n h (recursiveBlockReserve L E) E L ≤
      8192 * (L + (h + 1) * (E + h + Nat.clog 2 (L + E + 1) + 1)) :=
  Internal.scheduledBlockSeedBits_le n L E h length depth

end Algebraic.Cutwidth.Extractor
