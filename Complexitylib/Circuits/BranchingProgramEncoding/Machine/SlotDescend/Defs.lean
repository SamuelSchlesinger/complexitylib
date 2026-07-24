/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotStep.Defs

/-!
# Barrington recursive slot descent -- definitions

After the initial slot positioner captures one base-four digit, the preserved
address head sits on that digit's low bit. Descending to the next digit needs
only one left move, resetting the two one-bit latches, and another adjacent-bit
capture. This module defines that constant-cost machine layer.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Two-state controller for preparing the next lower base-four digit. -/
inductive PrepareNextSlotDigitPhase where
  | prepare
  | done
  deriving DecidableEq

/-- The preparation controller has exactly two states. -/
instance instFintypePrepareNextSlotDigitPhase :
    Fintype PrepareNextSlotDigitPhase where
  elems := {.prepare, .done}
  complete := fun phase => by cases phase <;> simp

/-- Exact work frame after moving the address one cell left and blanking both
captured-bit latches. -/
def prepareNextSlotDigitWork {n : ℕ} (sourceIdx lowIdx highIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape :=
  fun i =>
    if i = sourceIdx then
      (work i).writeAndMove (TM.readBackWrite (work i).read) Dir3.left
    else if i = lowIdx ∨ i = highIdx then
      (work i).writeAndMove .blank Dir3.stay
    else
      (work i).writeAndMove (TM.readBackWrite (work i).read)
        (TM.idleDir (work i).read)

/-- Move the preserved address from the current low bit onto the next lower
digit's high bit while resetting both captured-bit latches to canonical zero. -/
def prepareNextSlotDigitTM {n : ℕ} (sourceIdx lowIdx highIdx : Fin n) : TM n where
  Q := PrepareNextSlotDigitPhase
  qstart := .prepare
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .prepare =>
        (.done,
          fun i =>
            if i = lowIdx ∨ i = highIdx then .blank
            else TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead,
          TM.idleDir iHead,
          fun i =>
            if i = sourceIdx then
              if wHeads i = Γ.start then Dir3.right else Dir3.left
            else TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    cases phase with
    | prepare =>
        refine ⟨TM.idleDir_right_of_start, ?_,
          TM.idleDir_right_of_start⟩
        intro i hi
        by_cases his : i = sourceIdx
        · subst i
          simp [hi]
        · simp [his, TM.idleDir_right_of_start hi]
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Prepare the next digit, then capture its high and low bits. -/
def recaptureSlotBitsTM {n : ℕ} (layout : BarringtonSlotLayout n) : TM n :=
  TM.seqTM
    (prepareNextSlotDigitTM layout.sourceIdx layout.lowIdx layout.highIdx)
    (captureSlotBitsTM layout.sourceIdx layout.lowIdx layout.highIdx)

/-- Exact runtime of one recursive digit preparation and capture. -/
def recaptureSlotBitsTime : ℕ :=
  1 + 1 + 3

/-- Safe all-prefix space envelope for one recursive digit preparation and
capture. -/
def recaptureSlotBitsSpace (initialSpace : ℕ) : ℕ :=
  initialSpace + recaptureSlotBitsTime

/-- Capture the next lower slot digit and dispatch through its semantic raw
bits and the current reflection flag. -/
def barringtonNextSlotBranchTM {n : ℕ}
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n) : TM n :=
  TM.seqTM (recaptureSlotBitsTM layout)
    (barringtonSlotBranchTM layout.lowIdx layout.highIdx reversed
      onLeft onRight onInverseLeft onInverseRight)

/-- Runtime of recursive digit capture, two dispatch transitions, and the
selected continuation. -/
def barringtonNextSlotBranchTime (selectedTime : ℕ) : ℕ :=
  recaptureSlotBitsTime + 1 + (selectedTime + 2)

end Machine

end BPCode

end Complexity
