/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotDescend.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotDescend.Internal

/-!
# Barrington recursive slot descent

This module exposes the constant-cost preparation step used after the initial
slot digit has been captured.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- Move onto the next lower digit's high bit and reset both captured-bit
latches in one transition. -/
theorem prepareNextSlotDigitTM_hoareTime
    (sourceIdx lowIdx highIdx : Fin n)
    (hsl : sourceIdx ≠ lowIdx) (hsh : sourceIdx ≠ highIdx)
    (low high : Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsource : (work₀ sourceIdx).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (hlow : (work₀ lowIdx).HasBinaryNat (if low then 1 else 0))
    (hhigh : (work₀ highIdx).HasBinaryNat (if high then 1 else 0))
    (houtput : out₀.read ≠ Γ.start) :
    (prepareNextSlotDigitTM sourceIdx lowIdx highIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work sourceIdx = (work₀ sourceIdx).move Dir3.left ∧
        (work lowIdx).HasBinaryNat 0 ∧
        (work highIdx).HasBinaryNat 0 ∧
        (∀ i, i ≠ sourceIdx → i ≠ lowIdx → i ≠ highIdx →
          work i = work₀ i) ∧
        out = out₀)
      1 :=
  prepareNextSlotDigitTM_hoareTime_internal sourceIdx lowIdx highIdx hsl hsh
    low high inp₀ work₀ out₀ hinput hsource hwork hlow hhigh houtput

/-- One constant-cost recursive descent exposes exactly the next lower raw
base-four digit of the preserved canonical slot address. -/
theorem recaptureSlotBitsTM_hoareTime
    (layout : BarringtonSlotLayout n) (slotValue fuel : ℕ)
    (previousLow previousHigh : Bool)
    (original : Tape)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : original.HasBinaryNat slotValue)
    (hsourceHead : (work₀ layout.sourceIdx).head =
      original.head + 2 * (fuel + 1))
    (hsourceCells : (work₀ layout.sourceIdx).cells = original.cells)
    (hlow : (work₀ layout.lowIdx).HasBinaryNat
      (if previousLow then 1 else 0))
    (hhigh : (work₀ layout.highIdx).HasBinaryNat
      (if previousHigh then 1 else 0))
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (recaptureSlotBitsTM layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work layout.sourceIdx).head = original.head + 2 * fuel ∧
        (work layout.sourceIdx).cells = original.cells ∧
        (work layout.lowIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
        (work layout.highIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
        (∀ i, i ≠ layout.sourceIdx → i ≠ layout.lowIdx →
          i ≠ layout.highIdx → work i = work₀ i) ∧
        out = out₀)
      recaptureSlotBitsTime :=
  recaptureSlotBitsTM_hoareTime_internal layout slotValue fuel previousLow
    previousHigh original inp₀ work₀ out₀ hinput hslot hsourceHead hsourceCells
    hlow hhigh hwork houtput

/-- Recursive digit capture has a constant additive all-prefix space cost. -/
theorem recaptureSlotBitsTM_hoareTimeSpace
    (layout : BarringtonSlotLayout n) (slotValue fuel : ℕ)
    (previousLow previousHigh : Bool)
    (original : Tape) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : original.HasBinaryNat slotValue)
    (hsourceHead : (work₀ layout.sourceIdx).head =
      original.head + 2 * (fuel + 1))
    (hsourceCells : (work₀ layout.sourceIdx).cells = original.cells)
    (hlow : (work₀ layout.lowIdx).HasBinaryNat
      (if previousLow then 1 else 0))
    (hhigh : (work₀ layout.highIdx).HasBinaryNat
      (if previousHigh then 1 else 0))
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (recaptureSlotBitsTM layout).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work layout.sourceIdx).head = original.head + 2 * fuel ∧
        (work layout.sourceIdx).cells = original.cells ∧
        (work layout.lowIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
        (work layout.highIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
        (∀ i, i ≠ layout.sourceIdx → i ≠ layout.lowIdx →
          i ≠ layout.highIdx → work i = work₀ i) ∧
        out = out₀)
      recaptureSlotBitsTime inputLength
      (recaptureSlotBitsSpace initialSpace) :=
  recaptureSlotBitsTM_hoareTimeSpace_internal layout slotValue fuel previousLow
    previousHigh original inputLength initialSpace inp₀ work₀ out₀ hinput hslot
    hsourceHead hsourceCells hlow hhigh hwork houtput hworkSpace hinputSpace

/-- Recursive digit capture feeds its exact raw bits to the selected four-way
continuation without increasing the continuation's space budget. -/
theorem barringtonNextSlotBranchTM_selected_hoareTimeSpace
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n)
    (slotValue fuel : ℕ) (previousLow previousHigh : Bool)
    (original : Tape) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : original.HasBinaryNat slotValue)
    (hsourceHead : (work₀ layout.sourceIdx).head =
      original.head + 2 * (fuel + 1))
    (hsourceCells : (work₀ layout.sourceIdx).cells = original.cells)
    (hlow : (work₀ layout.lowIdx).HasBinaryNat
      (if previousLow then 1 else 0))
    (hhigh : (work₀ layout.highIdx).HasBinaryNat
      (if previousHigh then 1 else 0))
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1)
    {post : TapePred n} {selectedTime : ℕ}
    (hselected :
      (barringtonSlotContinuation reversed (slotValue.testBit (2 * fuel))
        (slotValue.testBit (2 * fuel + 1)) onLeft onRight onInverseLeft
        onInverseRight).HoareTimeSpace
          (fun inp work out =>
            inp = inp₀ ∧
            (work layout.sourceIdx).head = original.head + 2 * fuel ∧
            (work layout.sourceIdx).cells = original.cells ∧
            (work layout.lowIdx).HasBinaryNat
              (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
            (work layout.highIdx).HasBinaryNat
              (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
            (∀ i, i ≠ layout.sourceIdx → i ≠ layout.lowIdx →
              i ≠ layout.highIdx → work i = work₀ i) ∧
            out = out₀)
          post selectedTime inputLength
          (recaptureSlotBitsSpace initialSpace)) :
    (barringtonNextSlotBranchTM layout reversed onLeft onRight onInverseLeft
      onInverseRight).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        post (barringtonNextSlotBranchTime selectedTime) inputLength
        (recaptureSlotBitsSpace initialSpace) :=
  barringtonNextSlotBranchTM_selected_hoareTimeSpace_internal layout reversed
    onLeft onRight onInverseLeft onInverseRight slotValue fuel previousLow
    previousHigh original inputLength initialSpace inp₀ work₀ out₀ hinput hslot
    hsourceHead hsourceCells hlow hhigh hwork houtput hworkSpace hinputSpace
    hselected

/-- Recursive digit capture selects the semantic child named by the slot
cursor, hiding raw bit and reflection arithmetic from the caller. -/
theorem barringtonNextSlotBranchTM_cursor_hoareTimeSpace
    (layout : BarringtonSlotLayout n) (cursor : BarringtonSlotCursor)
    (onLeft onRight onInverseLeft onInverseRight : TM n)
    (fuel : ℕ) (previousLow previousHigh : Bool)
    (original : Tape) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : original.HasBinaryNat cursor.slot)
    (hsourceHead : (work₀ layout.sourceIdx).head =
      original.head + 2 * (fuel + 1))
    (hsourceCells : (work₀ layout.sourceIdx).cells = original.cells)
    (hlow : (work₀ layout.lowIdx).HasBinaryNat
      (if previousLow then 1 else 0))
    (hhigh : (work₀ layout.highIdx).HasBinaryNat
      (if previousHigh then 1 else 0))
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1)
    {post : TapePred n} {selectedTime : ℕ}
    (hselected :
      (if cursor.selectsInverse fuel then
          if cursor.selectsRight fuel then onInverseRight else onInverseLeft
        else if cursor.selectsRight fuel then onRight else onLeft
      ).HoareTimeSpace
          (fun inp work out =>
            inp = inp₀ ∧
            (work layout.sourceIdx).head = original.head + 2 * fuel ∧
            (work layout.sourceIdx).cells = original.cells ∧
            (work layout.lowIdx).HasBinaryNat
              (if cursor.slot.testBit (2 * fuel) then 1 else 0) ∧
            (work layout.highIdx).HasBinaryNat
              (if cursor.slot.testBit (2 * fuel + 1) then 1 else 0) ∧
            (∀ i, i ≠ layout.sourceIdx → i ≠ layout.lowIdx →
              i ≠ layout.highIdx → work i = work₀ i) ∧
            out = out₀)
          post selectedTime inputLength
          (recaptureSlotBitsSpace initialSpace)) :
    (barringtonNextSlotBranchTM layout cursor.reversed onLeft onRight
      onInverseLeft onInverseRight).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        post (barringtonNextSlotBranchTime selectedTime) inputLength
        (recaptureSlotBitsSpace initialSpace) := by
  rw [← barringtonSlotContinuation_cursor cursor fuel onLeft onRight
    onInverseLeft onInverseRight] at hselected
  exact barringtonNextSlotBranchTM_selected_hoareTimeSpace layout
    cursor.reversed onLeft onRight onInverseLeft onInverseRight cursor.slot fuel
    previousLow previousHigh original inputLength initialSpace inp₀ work₀ out₀
    hinput hslot hsourceHead hsourceCells hlow hhigh hwork houtput hworkSpace
    hinputSpace hselected

/-- Preparing a lower digit never moves the output head left. -/
theorem prepareNextSlotDigitTM_isTransducer
    (sourceIdx lowIdx highIdx : Fin n) :
    (prepareNextSlotDigitTM sourceIdx lowIdx highIdx).IsTransducer :=
  prepareNextSlotDigitTM_isTransducer_internal sourceIdx lowIdx highIdx

/-- Recursive digit recapture never moves the output head left. -/
theorem recaptureSlotBitsTM_isTransducer
    (layout : BarringtonSlotLayout n) :
    (recaptureSlotBitsTM layout).IsTransducer :=
  recaptureSlotBitsTM_isTransducer_internal layout

/-- Recursive digit recapture and dispatch remain one-way on output when all
four continuations are. -/
theorem barringtonNextSlotBranchTM_isTransducer
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    {onLeft onRight onInverseLeft onInverseRight : TM n}
    (hleft : onLeft.IsTransducer) (hright : onRight.IsTransducer)
    (hinverseLeft : onInverseLeft.IsTransducer)
    (hinverseRight : onInverseRight.IsTransducer) :
    (barringtonNextSlotBranchTM layout reversed onLeft onRight onInverseLeft
      onInverseRight).IsTransducer :=
  barringtonNextSlotBranchTM_isTransducer_internal layout reversed hleft hright
    hinverseLeft hinverseRight

end Machine

end BPCode

end Complexity
