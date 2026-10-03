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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Run.Correctness
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec

/-!
# Exact computation of the statistical scheduled extractor

The complete canonical seed word supplies precisely the seeds consumed by
the internal loop. The untouched final two field words then drive the
shared one-shot leaf extractor. The result is the statistical output tuple
serialized in block order, including zero-depth and empty output cases.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem scheduledBlockExtractorBits_eq_scheduledBlockExtractor (n h Q E ell : Nat)
    (x : Fin n → Bool)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    scheduledBlockExtractorBits n h Q E ell (List.ofFn x)
        (encodeScheduledBlockSeeds n h Q E ell seeds) =
      (List.ofFn fun i => List.ofFn fun j =>
        decide (scheduledBlockExtractor n h Q E ell x seeds i j = 1)).flatten := by
  rw [scheduledBlockExtractorBits, encodeScheduledBlockSeeds_append, List.append_assoc,
    scheduledBlockRun_eq_recursiveBlockMap]
  dsimp only [scheduledBlockFinish]
  rw [← BinaryFieldCodec.length_encode _ seeds.2.1, List.take_left, List.drop_left]
  rw [oneShotBlockExtractorBits_eq_decoded
      (recursiveBlockWidth (scheduledBlockInitialWidth n h Q E) h Q E h) ell E
      (recursiveBlockMap (fun x seed (_ : Fin 1) => scheduledBlockInitial n h Q E x seed)
        (scheduledBlockStep n h Q E) h x seeds.1) seeds.2
      (List.replicate (recursiveBlockCount 1 h) true) (by simp)]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
