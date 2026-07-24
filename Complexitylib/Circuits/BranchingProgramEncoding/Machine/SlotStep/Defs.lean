/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotBranch.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotCapture.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotPosition.Defs

/-!
# Barrington initial slot step -- definitions

The initial recursive slot step positions a preserved canonical address on its
highest relevant base-four digit, captures that digit's two raw bits, and then
hands the canonical bit tapes to the four-way continuation dispatcher.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Five structurally distinct tapes used by the initial slot controller.

The role order is source address, loop counter, preserved fuel, captured low
bit, and captured high bit. -/
structure BarringtonSlotLayout (controllerTapes : ℕ) where
  /-- Injective assignment of the five logical slot-controller roles. -/
  roles : Fin 5 ↪ Fin controllerTapes

/-- Preserved binary slot-address tape. -/
def BarringtonSlotLayout.sourceIdx
    (layout : BarringtonSlotLayout controllerTapes) : Fin controllerTapes :=
  layout.roles 0

/-- Scratch counter used to position the source address. -/
def BarringtonSlotLayout.counterIdx
    (layout : BarringtonSlotLayout controllerTapes) : Fin controllerTapes :=
  layout.roles 1

/-- Preserved binary recursion fuel. -/
def BarringtonSlotLayout.limitIdx
    (layout : BarringtonSlotLayout controllerTapes) : Fin controllerTapes :=
  layout.roles 2

/-- Canonical captured low-bit tape. -/
def BarringtonSlotLayout.lowIdx
    (layout : BarringtonSlotLayout controllerTapes) : Fin controllerTapes :=
  layout.roles 3

/-- Canonical captured high-bit tape. -/
def BarringtonSlotLayout.highIdx
    (layout : BarringtonSlotLayout controllerTapes) : Fin controllerTapes :=
  layout.roles 4

/-- Position the address on the current high bit, then capture the adjacent
high/low base-four digit. -/
def positionCaptureSlotBitsTM {n : ℕ} (layout : BarringtonSlotLayout n) : TM n :=
  TM.seqTM
    (positionSlotTM layout.sourceIdx layout.counterIdx layout.limitIdx)
    (captureSlotBitsTM layout.sourceIdx layout.lowIdx layout.highIdx)

/-- Exact time bound for initial positioning and adjacent bit capture. -/
def positionCaptureSlotBitsTime (fuel : ℕ) : ℕ :=
  positionSlotTime fuel + 1 + 3

/-- All-prefix space budget for initial positioning and bit capture. -/
def positionCaptureSlotBitsSpace (initialSpace fuel : ℕ) : ℕ :=
  positionSlotSpace initialSpace fuel + 3

/-- Position and capture the current raw digit, then dispatch through its two
bits and the finite-control reflection flag. -/
def barringtonInitialSlotBranchTM {n : ℕ}
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n) : TM n :=
  TM.seqTM (positionCaptureSlotBitsTM layout)
    (barringtonSlotBranchTM layout.lowIdx layout.highIdx reversed
      onLeft onRight onInverseLeft onInverseRight)

/-- Time bound of initial positioning, capture, two dispatch transitions, and
the selected continuation. -/
def barringtonInitialSlotBranchTime (fuel selectedTime : ℕ) : ℕ :=
  positionCaptureSlotBitsTime fuel + 1 + (selectedTime + 2)

end Machine

end BPCode

end Complexity
