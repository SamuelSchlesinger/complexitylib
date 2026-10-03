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
public import Complexitylib.Tactic.PolyTime.Init
public import Mathlib.Order.Filter.AtTopBot.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Program.Family.Internal

/-!
# A uniform polynomial-time evaluator for each asymptotic extractor family

For fixed natural parameters `a,e`, one string function computes the entire
recursive extractor from its source and seed word. For every sufficiently
large source length, it agrees with the specified asymptotic extractor on
all Boolean inputs and all canonical seeds. The seed codec is bijective at
the exact proved seed length, so canonical words cover that entire seed space.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Filter

/-- The complete fixed-family bit program is polynomial-time in its source and seed word. -/
@[polytime] theorem polylogBlockExtractorProgram_mem_FP (a e : Nat) :
    polylogBlockExtractorProgram a e ∈ FP :=
  Internal.polylogBlockExtractorProgram_mem_FP a e

/-- At all sufficiently large lengths, the single program computes every coordinate
of the specified family on all source inputs and canonically encoded seeds. -/
theorem eventually_polylogBlockExtractorProgram (a e : Nat) :
    ∀ᶠ n : Nat in atTop, ∀ (x : Fin n → Bool) (seeds : PolylogBlockSeeds a e n),
      polylogBlockExtractorProgram a e
          (pair (List.ofFn x) (encodeScheduledBlockSeeds n (polylogBlockDepth a n)
            (polylogBlockReserve a e n) (polylogBlockErrorExponent a e n)
            (polylogBlockLength n) seeds)) =
        (List.ofFn fun i => List.ofFn fun j =>
          decide (polylogBlockExtractor a e n x seeds i j = 1)).flatten :=
  Internal.eventually_polylogBlockExtractorProgram a e

end Algebraic.Cutwidth.Extractor
