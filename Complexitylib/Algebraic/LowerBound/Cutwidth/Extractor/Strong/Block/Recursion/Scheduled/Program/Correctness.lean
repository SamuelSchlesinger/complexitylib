/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Correctness.Internal

/-!
# The complete bit program computes the specified statistical extractor

At canonical seed words, the output is exactly the scheduled extractor's
tuple serialized in block order, with `ZMod 2` values represented by Boolean
bits. This identity imposes no entropy or reserve premise and needs no
field enumeration. The statistical and uniform runtime bounds can therefore
be applied to the same construction.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The complete runtime program serializes exactly the actual statistical output tuple. -/
theorem scheduledBlockExtractorBits_eq_scheduledBlockExtractor (n h Q E ell : Nat)
    (x : Fin n → Bool)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    scheduledBlockExtractorBits n h Q E ell (List.ofFn x)
        (encodeScheduledBlockSeeds n h Q E ell seeds) =
      (List.ofFn fun i => List.ofFn fun j =>
        decide (scheduledBlockExtractor n h Q E ell x seeds i j = 1)).flatten :=
  Internal.scheduledBlockExtractorBits_eq_scheduledBlockExtractor n h Q E ell x seeds

end Algebraic.Cutwidth.Extractor
