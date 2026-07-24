/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork.Defs

/-!
# Binary-bounded work-prefix blanking -- definitions

A reusable output probe may leave sparse data anywhere inside its advertised
work-space envelope. Clearing only an initial packed bitstring is therefore
insufficient before replay. This module blanks every cell in a prefix whose
length is stored on a canonical binary limit tape, then rewinds the target and
restores a zero scratch counter.
-/

namespace Complexity

namespace TM

/-- The target, loop counter, and preserved limit occupy distinct work tapes. -/
def BlankWorkPrefixDistinct {n : ℕ} (targetIdx counterIdx limitIdx : Fin n) :
    Prop :=
  targetIdx ≠ counterIdx ∧ targetIdx ≠ limitIdx ∧ counterIdx ≠ limitIdx

/-- Blank cells `1` through `count`, preserving every other cell. -/
def blankPrefixCells (cells : ℕ → Γ) (count : ℕ) : ℕ → Γ :=
  fun index =>
    if 1 ≤ index ∧ index ≤ count then Γ.blank else cells index

/-- Tape after blanking `count` cells from the left and advancing once past
that prefix. -/
def blankPrefixTape (tape : Tape) (count : ℕ) : Tape where
  head := count + 1
  cells := blankPrefixCells tape.cells count

/-- Tape after blanking a bounded prefix and rewinding its head to cell one. -/
def blankPrefixResultTape (tape : Tape) (count : ℕ) : Tape where
  head := 1
  cells := blankPrefixCells tape.cells count

/-- One transition blanks the target cell and moves its head right. -/
def blankWorkCellTM {n : ℕ} (targetIdx : Fin n) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun state inputHead workHeads outputHead =>
    if state then
      allIdle true inputHead workHeads outputHead
    else
      (true,
        fun i => if i = targetIdx then Γw.blank
          else readBackWrite (workHeads i),
        readBackWrite outputHead,
        idleDir inputHead,
        fun i => if i = targetIdx then Dir3.right
          else idleDir (workHeads i),
        idleDir outputHead)
  δ_right_of_start := by
    intro state inputHead workHeads outputHead
    by_cases hstate : state
    · simp [hstate, allIdle, idleDir]
    · simp only [hstate]
      refine ⟨idleDir_right_of_start, fun i hi => ?_,
        idleDir_right_of_start⟩
      by_cases hitarget : i = targetIdx
      · simp [hitarget]
      · simp [hitarget, idleDir_right_of_start hi]

/-- Count from zero to the preserved binary limit, blanking and advancing the
target once per iteration. -/
def blankWorkPrefixLoopTM {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n) : TM n :=
  binaryForTM (blankWorkCellTM targetIdx) counterIdx limitIdx

/-- Blank the binary-bounded prefix, rewind the target, and clear the loop
counter back to canonical zero. -/
def blankWorkPrefixTM {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n) : TM n :=
  seqTM (blankWorkPrefixLoopTM targetIdx counterIdx limitIdx)
    (seqTM (rewindWorkTM targetIdx) (clearWorkTM counterIdx))

/-- Rewind an arbitrarily positioned target before blanking its bounded
prefix. This is the replay-cleanup form used after a source transducer halts. -/
def rewindBlankWorkPrefixTM {n : ℕ}
    (targetIdx counterIdx limitIdx : Fin n) : TM n :=
  seqTM (rewindWorkTM targetIdx)
    (blankWorkPrefixTM targetIdx counterIdx limitIdx)

/-- Exact loop time before target rewind and counter cleanup. -/
def blankWorkPrefixLoopTime (limit : ℕ) : ℕ :=
  binaryForLoopTime (fun _ => 1) limit 0 limit

/-- Advertised complete runtime of bounded-prefix blanking. -/
def blankWorkPrefixTime (limit : ℕ) : ℕ :=
  blankWorkPrefixLoopTime limit + 1 + (limit + 3) + 1 +
    clearWorkTimeBound limit.bits.length

/-- All-prefix auxiliary-space envelope from an initial work-head bound. -/
def blankWorkPrefixSpace (initialSpace limit : ℕ) : ℕ :=
  max (initialSpace + limit + 2 * limit.size + 4)
    (max ((initialSpace + limit) + (limit + 3))
      (initialSpace + clearWorkTimeBound limit.bits.length))

/-- Exact advertised runtime for rewind followed by bounded-prefix blanking. -/
def rewindBlankWorkPrefixTime (headBound limit : ℕ) : ℕ :=
  headBound + 2 + 1 + blankWorkPrefixTime limit

/-- All-prefix envelope for rewind followed by bounded-prefix blanking. -/
def rewindBlankWorkPrefixSpace
    (initialSpace headBound limit : ℕ) : ℕ :=
  max (initialSpace + (headBound + 2))
    (blankWorkPrefixSpace initialSpace limit)

end TM

end Complexity
