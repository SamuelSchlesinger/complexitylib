/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Canonical binary addition — definitions

This module defines binary addition from the reusable canonical count-up loop.
The source tape is the preserved loop limit, the destination is incremented
once per source value, and a distinct scratch counter records loop progress.
After the loop, the scratch tape is cleared back to canonical zero.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- Add the preserved canonical binary source into the destination, leaving
the scratch counter equal to the source at loop exit. -/
def binaryAddLoopTM {n : ℕ}
    (srcIdx dstIdx counterIdx : Fin n) : TM n :=
  binaryForTM (binarySuccTM dstIdx) counterIdx srcIdx

/-- Add the preserved canonical binary source into the destination, then
restore the scratch counter to canonical zero. -/
def binaryAddIntoTM {n : ℕ}
    (srcIdx dstIdx counterIdx : Fin n) : TM n :=
  seqTM (binaryAddLoopTM srcIdx dstIdx counterIdx)
    (clearWorkTM counterIdx)

/-- Exact running time of the count-up loop used for binary addition. -/
def binaryAddLoopTime (srcValue dstValue : ℕ) : ℕ :=
  binaryForLoopTime (fun value => binarySuccTime (dstValue + value))
    srcValue 0 srcValue

/-- Time bound for binary addition, including the composition seam and
scratch clearing. -/
def binaryAddTime (srcValue dstValue : ℕ) : ℕ :=
  binaryAddLoopTime srcValue dstValue + 1 +
    clearWorkTimeBound srcValue.size

/-- Honest all-prefix space bound for the addition loop. It depends on the
binary widths of the source and largest destination value, not on total loop
runtime. -/
def binaryAddLoopSpace (initialSpace srcValue dstValue : ℕ) : ℕ :=
  initialSpace + 2 * srcValue.size + 2 * (dstValue + srcValue).size + 5

/-- All-prefix space bound for addition followed by scratch clearing. -/
def binaryAddSpace (initialSpace srcValue dstValue : ℕ) : ℕ :=
  binaryAddLoopSpace initialSpace srcValue dstValue +
    clearWorkTimeBound srcValue.size

end TM

end Complexity
