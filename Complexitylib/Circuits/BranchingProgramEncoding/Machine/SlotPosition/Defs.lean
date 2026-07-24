/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor.Defs

/-!
# Barrington slot positioning -- definitions

These constant-time bodies move a preserved binary slot-address cursor to the
right. A later binary count-up loop applies the two-cell body once per base-four
digit and then the one-cell body once, reaching the current high address bit.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Exact work frame after moving one designated head one cell right. -/
def moveSlotRightWork {n : ℕ} (sourceIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape :=
  Function.update work sourceIdx ((work sourceIdx).move Dir3.right)

/-- Controller for one rightward slot-head movement. -/
inductive MoveSlotRightPhase where
  | move
  | done
  deriving DecidableEq

/-- The one-cell movement controller has exactly two states. -/
instance instFintypeMoveSlotRightPhase : Fintype MoveSlotRightPhase where
  elems := {.move, .done}
  complete := fun phase => by cases phase <;> simp

/-- Move one designated work-tape head one cell right in one transition. -/
def moveSlotRightTM {n : ℕ} (sourceIdx : Fin n) : TM n where
  Q := MoveSlotRightPhase
  qstart := .move
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .move =>
        (.done, fun i => TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead, TM.idleDir iHead,
          fun i => if i = sourceIdx then Dir3.right else TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    cases phase with
    | move =>
        refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
        intro i hi
        by_cases his : i = sourceIdx
        · simp [his]
        · simp [his, TM.idleDir_right_of_start hi]
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Controller for advancing across one two-bit base-four digit. -/
inductive AdvanceSlotDigitPhase where
  | first
  | second
  | done
  deriving DecidableEq

/-- The two-cell digit movement controller has exactly three states. -/
instance instFintypeAdvanceSlotDigitPhase : Fintype AdvanceSlotDigitPhase where
  elems := {.first, .second, .done}
  complete := fun phase => by cases phase <;> simp

/-- Move one designated work-tape head two cells right in two transitions. -/
def advanceSlotDigitTM {n : ℕ} (sourceIdx : Fin n) : TM n where
  Q := AdvanceSlotDigitPhase
  qstart := .first
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .first =>
        (.second, fun i => TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead, TM.idleDir iHead,
          fun i => if i = sourceIdx then Dir3.right else TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .second =>
        (.done, fun i => TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead, TM.idleDir iHead,
          fun i => if i = sourceIdx then Dir3.right else TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    cases phase with
    | first | second =>
        refine ⟨TM.idleDir_right_of_start, ?_, TM.idleDir_right_of_start⟩
        intro i hi
        by_cases his : i = sourceIdx
        · simp [his]
        · simp [his, TM.idleDir_right_of_start hi]
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Binary count-up loop that advances the source head across one base-four
digit per iteration. -/
def positionSlotLoopTM {n : ℕ}
    (sourceIdx counterIdx limitIdx : Fin n) : TM n :=
  TM.binaryForTM (advanceSlotDigitTM sourceIdx) counterIdx limitIdx

/-- Runtime slot positioner: advance two cells per binary loop iteration, then
one more cell to land on bit `2 * fuel + 1`. -/
def positionSlotTM {n : ℕ} (sourceIdx counterIdx limitIdx : Fin n) : TM n :=
  TM.seqTM (positionSlotLoopTM sourceIdx counterIdx limitIdx)
    (moveSlotRightTM sourceIdx)

/-- Exact time of the binary loop that advances across `fuel` base-four
digits. -/
def positionSlotLoopTime (fuel : ℕ) : ℕ :=
  TM.binaryForLoopTime (fun _ => 2) fuel 0 fuel

/-- Exact time bound of loop positioning followed by the final one-cell move. -/
def positionSlotTime (fuel : ℕ) : ℕ :=
  positionSlotLoopTime fuel + 1 + 1

/-- Shared all-prefix space budget for positioning from a frame bounded by
`initialSpace`. The linear `2 * fuel` term is the address-head displacement;
the smaller `Nat.size` term covers the binary loop controller. -/
def positionSlotSpace (initialSpace fuel : ℕ) : ℕ :=
  initialSpace + 2 * fuel + 2 * fuel.size + 6

end Machine

end BPCode

end Complexity
