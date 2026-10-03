/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Family.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Codec.Defs
public import Complexitylib.Classes.P.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Correctness
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Asymptotics
import Complexitylib.Tactic.PolyTime

/-!
# Uniform computation of the fixed asymptotic extractor family

The family depth is a polynomial-time unary function of the input length.
For sufficiently large lengths, its depth fits the finite schedule, so the
total bit program computes exactly the specified asymptotic extractor on
every source and canonical seed word. This ties the asymptotic statistical
map to a single polynomial-time machine for each fixed family.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity Filter

theorem polylogBlockExtractorProgram_mem_FP (a e : Nat) : polylogBlockExtractorProgram a e ∈ FP := by
  unfold polylogBlockExtractorProgram
  apply scheduledBlockExtractorRuntime_mem_FP
  · unfold polylogBlockDepth polylogBlockLength
    polytime
  · polytime
  · polytime
  · polytime

theorem eventually_polylogBlockExtractorProgram (a e : Nat) :
    ∀ᶠ n : Nat in atTop, ∀ (x : Fin n → Bool) (seeds : PolylogBlockSeeds a e n),
      polylogBlockExtractorProgram a e
          (pair (List.ofFn x) (encodeScheduledBlockSeeds n (polylogBlockDepth a n)
            (polylogBlockReserve a e n) (polylogBlockErrorExponent a e n)
            (polylogBlockLength n) seeds)) =
        (List.ofFn fun i => List.ofFn fun j =>
          decide (polylogBlockExtractor a e n x seeds i j = 1)).flatten := by
  filter_upwards [eventually_polylogBlockDepth_le a] with n depth
  intro x seeds
  simp only [polylogBlockExtractorProgram, pairFst_pair, pairSnd_pair, List.length_ofFn]
  rw [scheduledBlockExtractorRuntime_of_depth_le _ _ _ _ (by simpa [polylogBlockLength] using depth)]
  simp only [List.length_ofFn]
  change scheduledBlockExtractorBits n (polylogBlockDepth a n)
    (polylogBlockReserve a e n) (polylogBlockErrorExponent a e n) (polylogBlockLength n)
    (List.ofFn x) (encodeScheduledBlockSeeds n (polylogBlockDepth a n)
      (polylogBlockReserve a e n) (polylogBlockErrorExponent a e n)
      (polylogBlockLength n) seeds) = _
  rw [scheduledBlockExtractorBits_eq_scheduledBlockExtractor n (polylogBlockDepth a n)
      (polylogBlockReserve a e n) (polylogBlockErrorExponent a e n)
      (polylogBlockLength n) x seeds]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
