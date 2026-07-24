/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotCapture.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotCapture.Internal

/-!
# Barrington slot-bit capture

This module exposes the framed one-step primitive that captures a positioned
binary address bit into a canonical controller tape.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- A positioned tape with the cells of a canonical binary tape exposes the
corresponding `Nat.testBit`, including implicit false high bits. -/
theorem slotBitAtHead_eq_testBit_of_cells
    (tape original : Tape) (value offset : ℕ)
    (hvalue : original.HasBinaryNat value)
    (hcells : tape.cells = original.cells)
    (hhead : tape.head = offset + 1) :
    slotBitAtHead tape = value.testBit offset :=
  slotBitAtHead_eq_testBit_of_cells_internal tape original value offset hvalue
    hcells hhead

/-- A canonical binary tape positioned on bit `offset` exposes exactly
`Nat.testBit value offset`; positions beyond the canonical bit string read as
false through the terminating blank. -/
theorem slotBitAtHead_eq_testBit
    (tape : Tape) (value offset : ℕ)
    (hvalue : tape.HasBinaryNat value)
    (hhead : tape.head = offset + 1) :
    slotBitAtHead tape = value.testBit offset :=
  slotBitAtHead_eq_testBit_internal tape value offset hvalue hhead

/-- One positioned source symbol becomes a canonical Boolean controller tape;
the source may simultaneously move one cell left. -/
theorem captureSlotBitTM_hoareTime
    (sourceIdx targetIdx : Fin n) (hne : sourceIdx ≠ targetIdx)
    (moveLeft : Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsource : (work₀ sourceIdx).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (hzero : (work₀ targetIdx).HasBinaryNat 0)
    (houtput : out₀.read ≠ Γ.start) :
    (captureSlotBitTM sourceIdx targetIdx moveLeft).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work sourceIdx =
          (if moveLeft then (work₀ sourceIdx).move Dir3.left
           else work₀ sourceIdx) ∧
        (work targetIdx).HasBinaryNat
          (if slotBitAtHead (work₀ sourceIdx) then 1 else 0) ∧
        (∀ i, i ≠ sourceIdx → i ≠ targetIdx → work i = work₀ i) ∧
        out = out₀)
      1 :=
  captureSlotBitTM_hoareTime_internal sourceIdx targetIdx hne moveLeft inp₀
    work₀ out₀ hinput hsource hwork hzero houtput

/-- A positioned capture adds at most one cell to the starting all-prefix
auxiliary-space budget. -/
theorem captureSlotBitTM_hoareTimeSpace
    (sourceIdx targetIdx : Fin n) (hne : sourceIdx ≠ targetIdx)
    (moveLeft : Bool) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsource : (work₀ sourceIdx).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (hzero : (work₀ targetIdx).HasBinaryNat 0)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (captureSlotBitTM sourceIdx targetIdx moveLeft).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (captureSlotBitTM sourceIdx targetIdx moveLeft).Q)
        |>.WithinAuxSpace inputLength initialSpace) :
    (captureSlotBitTM sourceIdx targetIdx moveLeft).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work sourceIdx =
          (if moveLeft then (work₀ sourceIdx).move Dir3.left
           else work₀ sourceIdx) ∧
        (work targetIdx).HasBinaryNat
          (if slotBitAtHead (work₀ sourceIdx) then 1 else 0) ∧
        (∀ i, i ≠ sourceIdx → i ≠ targetIdx → work i = work₀ i) ∧
        out = out₀)
      1 inputLength (initialSpace + 1) :=
  captureSlotBitTM_hoareTimeSpace_internal sourceIdx targetIdx hne moveLeft
    inputLength initialSpace inp₀ work₀ out₀ hinput hsource hwork hzero
    houtput hinitial

/-- Capturing one adjacent base-four digit costs exactly three framed
transitions and leaves the source head on its low bit. -/
theorem captureSlotBitsTM_hoareTime
    (sourceIdx lowIdx highIdx : Fin n)
    (hsl : sourceIdx ≠ lowIdx) (hsh : sourceIdx ≠ highIdx)
    (hlh : lowIdx ≠ highIdx)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceHigh : (work₀ sourceIdx).read ≠ Γ.start)
    (hsourceLow : ((work₀ sourceIdx).move Dir3.left).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (hlowZero : (work₀ lowIdx).HasBinaryNat 0)
    (hhighZero : (work₀ highIdx).HasBinaryNat 0)
    (houtput : out₀.read ≠ Γ.start) :
    (captureSlotBitsTM sourceIdx lowIdx highIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work sourceIdx = (work₀ sourceIdx).move Dir3.left ∧
        (work lowIdx).HasBinaryNat
          (if slotBitAtHead ((work₀ sourceIdx).move Dir3.left) then 1 else 0) ∧
        (work highIdx).HasBinaryNat
          (if slotBitAtHead (work₀ sourceIdx) then 1 else 0) ∧
        (∀ i, i ≠ sourceIdx → i ≠ lowIdx → i ≠ highIdx →
          work i = work₀ i) ∧
        out = out₀)
      3 :=
  captureSlotBitsTM_hoareTime_internal sourceIdx lowIdx highIdx hsl hsh hlh
    inp₀ work₀ out₀ hinput hsourceHigh hsourceLow hwork hlowZero hhighZero
    houtput

/-- Adjacent high/low capture adds at most three cells to the starting
all-prefix auxiliary-space budget. -/
theorem captureSlotBitsTM_hoareTimeSpace
    (sourceIdx lowIdx highIdx : Fin n)
    (hsl : sourceIdx ≠ lowIdx) (hsh : sourceIdx ≠ highIdx)
    (hlh : lowIdx ≠ highIdx)
    (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceHigh : (work₀ sourceIdx).read ≠ Γ.start)
    (hsourceLow : ((work₀ sourceIdx).move Dir3.left).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (hlowZero : (work₀ lowIdx).HasBinaryNat 0)
    (hhighZero : (work₀ highIdx).HasBinaryNat 0)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (captureSlotBitsTM sourceIdx lowIdx highIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (captureSlotBitsTM sourceIdx lowIdx highIdx).Q)
        |>.WithinAuxSpace inputLength initialSpace) :
    (captureSlotBitsTM sourceIdx lowIdx highIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work sourceIdx = (work₀ sourceIdx).move Dir3.left ∧
        (work lowIdx).HasBinaryNat
          (if slotBitAtHead ((work₀ sourceIdx).move Dir3.left) then 1 else 0) ∧
        (work highIdx).HasBinaryNat
          (if slotBitAtHead (work₀ sourceIdx) then 1 else 0) ∧
        (∀ i, i ≠ sourceIdx → i ≠ lowIdx → i ≠ highIdx →
          work i = work₀ i) ∧
        out = out₀)
      3 inputLength (initialSpace + 3) :=
  captureSlotBitsTM_hoareTimeSpace_internal sourceIdx lowIdx highIdx hsl hsh
    hlh inputLength initialSpace inp₀ work₀ out₀ hinput hsourceHigh
    hsourceLow hwork hlowZero hhighZero houtput hinitial

/-- Slot-bit capture never moves the output head left. -/
theorem captureSlotBitTM_isTransducer
    (sourceIdx targetIdx : Fin n) (moveLeft : Bool) :
    (captureSlotBitTM sourceIdx targetIdx moveLeft).IsTransducer :=
  captureSlotBitTM_isTransducer_internal sourceIdx targetIdx moveLeft

/-- Adjacent high/low capture never moves the output head left. -/
theorem captureSlotBitsTM_isTransducer
    (sourceIdx lowIdx highIdx : Fin n) :
    (captureSlotBitsTM sourceIdx lowIdx highIdx).IsTransducer :=
  captureSlotBitsTM_isTransducer_internal sourceIdx lowIdx highIdx

end Machine

end BPCode

end Complexity
