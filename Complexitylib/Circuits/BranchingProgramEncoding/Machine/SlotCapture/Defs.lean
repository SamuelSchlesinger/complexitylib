/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators

/-!
# Barrington slot-bit capture -- definitions

One transition copies the Boolean value under a positioned binary slot tape
head into a canonical one-bit controller tape. The source head can either stay
put or move one cell left, supporting high-then-low base-four digit scans.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Interpret only `1` as true; canonical `0` and implicit blank high bits are
both false. -/
def slotBitAtHead (tape : Tape) : Bool :=
  tape.read == Γ.one

/-- Writable symbol used for a canonical captured Boolean tape. -/
def slotBitWrite : Bool → Γw
  | false => .blank
  | true => .one

/-- Two-state controller for one positioned slot-bit capture. -/
inductive SlotBitCapturePhase where
  | capture
  | done
  deriving DecidableEq

/-- The capture controller has exactly two states. -/
instance instFintypeSlotBitCapturePhase : Fintype SlotBitCapturePhase where
  elems := {.capture, .done}
  complete := fun phase => by cases phase <;> simp

/-- Exact work frame produced by one slot-bit capture. -/
def captureSlotBitWork {n : ℕ} (sourceIdx targetIdx : Fin n)
    (moveLeft : Bool) (work : Fin n → Tape) : Fin n → Tape :=
  fun i =>
    if i = sourceIdx then
      (work i).writeAndMove (TM.readBackWrite (work i).read)
        (if moveLeft then Dir3.left else Dir3.stay)
    else if i = targetIdx then
      (work i).writeAndMove (slotBitWrite (slotBitAtHead (work sourceIdx)))
        Dir3.stay
    else
      (work i).writeAndMove (TM.readBackWrite (work i).read)
        (TM.idleDir (work i).read)

/-- Capture the bit currently under `sourceIdx` into the canonical-zero tape
`targetIdx`, optionally moving the source head one cell left. -/
def captureSlotBitTM {n : ℕ} (sourceIdx targetIdx : Fin n)
    (moveLeft : Bool) : TM n where
  Q := SlotBitCapturePhase
  qstart := .capture
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .capture =>
        if wHeads sourceIdx = Γ.start then
          TM.allIdle .capture iHead wHeads oHead
        else
          (.done,
            fun i =>
              if i = targetIdx then
                slotBitWrite (wHeads sourceIdx == Γ.one)
              else
                TM.readBackWrite (wHeads i),
            TM.readBackWrite oHead,
            TM.idleDir iHead,
            fun i =>
              if moveLeft && i = sourceIdx then Dir3.left
              else TM.idleDir (wHeads i),
            TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    cases phase with
    | capture =>
        dsimp only
        split
        · exact TM.rightOfStart_allIdle iHead wHeads oHead
        · next hsource =>
          refine ⟨TM.idleDir_right_of_start, ?_,
            TM.idleDir_right_of_start⟩
          intro i hi
          cases moveLeft
          · exact TM.idleDir_right_of_start hi
          · by_cases his : i = sourceIdx
            · subst i
              exact absurd hi hsource
            · simp [his, TM.idleDir_right_of_start hi]
    | done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-- Exact work frame after capturing the high bit, moving the source left, and
then capturing the adjacent low bit. -/
def captureSlotBitsWork {n : ℕ} (sourceIdx lowIdx highIdx : Fin n)
    (work : Fin n → Tape) : Fin n → Tape :=
  captureSlotBitWork sourceIdx lowIdx false
    (captureSlotBitWork sourceIdx highIdx true work)

/-- Capture one adjacent base-four address digit, high bit first and then low
bit, leaving the preserved source head on the low bit. -/
def captureSlotBitsTM {n : ℕ} (sourceIdx lowIdx highIdx : Fin n) : TM n :=
  TM.seqTM (captureSlotBitTM sourceIdx highIdx true)
    (captureSlotBitTM sourceIdx lowIdx false)

end Machine

end BPCode

end Complexity
