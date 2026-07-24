/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotStep.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotStep.Internal

/-!
# Barrington initial slot step

This module exposes the end-to-end contract from a parked binary address to
the two canonical raw bits consumed by the recursive four-way dispatcher.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- Initial positioning and capture expose exactly the low and high raw bits
of the requested base-four slot digit. -/
theorem positionCaptureSlotBitsTM_hoareTime
    (layout : BarringtonSlotLayout n) (slotValue fuel : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : (work₀ layout.sourceIdx).HasBinaryNat slotValue)
    (hcounter : (work₀ layout.counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ layout.limitIdx).HasBinaryNat fuel)
    (hlowZero : (work₀ layout.lowIdx).HasBinaryNat 0)
    (hhighZero : (work₀ layout.highIdx).HasBinaryNat 0)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (positionCaptureSlotBitsTM layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work layout.sourceIdx).head =
          (work₀ layout.sourceIdx).head + 2 * fuel ∧
        (work layout.sourceIdx).cells = (work₀ layout.sourceIdx).cells ∧
        (work layout.counterIdx).HasBinaryNat fuel ∧
        work layout.limitIdx = work₀ layout.limitIdx ∧
        (work layout.lowIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
        (work layout.highIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
        (∀ i, i ≠ layout.sourceIdx → i ≠ layout.counterIdx →
          i ≠ layout.limitIdx → i ≠ layout.lowIdx → i ≠ layout.highIdx →
          work i = work₀ i) ∧
        out = out₀)
      (positionCaptureSlotBitsTime fuel) :=
  positionCaptureSlotBitsTM_hoareTime_internal layout slotValue fuel inp₀ work₀
    out₀ hinput hslot hcounter hlimit hlowZero hhighZero hwork houtput

/-- Initial positioning and capture retain a tight all-prefix space bound:
positioning's certified budget plus the three capture transitions. -/
theorem positionCaptureSlotBitsTM_hoareTimeSpace
    (layout : BarringtonSlotLayout n) (slotValue fuel inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : (work₀ layout.sourceIdx).HasBinaryNat slotValue)
    (hcounter : (work₀ layout.counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ layout.limitIdx).HasBinaryNat fuel)
    (hlowZero : (work₀ layout.lowIdx).HasBinaryNat 0)
    (hhighZero : (work₀ layout.highIdx).HasBinaryNat 0)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (positionCaptureSlotBitsTM layout).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work layout.sourceIdx).head =
          (work₀ layout.sourceIdx).head + 2 * fuel ∧
        (work layout.sourceIdx).cells = (work₀ layout.sourceIdx).cells ∧
        (work layout.counterIdx).HasBinaryNat fuel ∧
        work layout.limitIdx = work₀ layout.limitIdx ∧
        (work layout.lowIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
        (work layout.highIdx).HasBinaryNat
          (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
        (∀ i, i ≠ layout.sourceIdx → i ≠ layout.counterIdx →
          i ≠ layout.limitIdx → i ≠ layout.lowIdx → i ≠ layout.highIdx →
          work i = work₀ i) ∧
        out = out₀)
      (positionCaptureSlotBitsTime fuel) inputLength
      (positionCaptureSlotBitsSpace initialSpace fuel) :=
  positionCaptureSlotBitsTM_hoareTimeSpace_internal layout slotValue fuel
    inputLength initialSpace inp₀ work₀ out₀ hinput hslot hcounter hlimit
    hlowZero hhighZero hwork houtput hworkSpace hinputSpace

/-- Initial positioning and capture feed their exact raw bits to the selected
four-way continuation. -/
theorem barringtonInitialSlotBranchTM_selected_hoareTime
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n)
    (slotValue fuel : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : (work₀ layout.sourceIdx).HasBinaryNat slotValue)
    (hcounter : (work₀ layout.counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ layout.limitIdx).HasBinaryNat fuel)
    (hlowZero : (work₀ layout.lowIdx).HasBinaryNat 0)
    (hhighZero : (work₀ layout.highIdx).HasBinaryNat 0)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    {post : TapePred n} {selectedTime : ℕ}
    (hselected :
      (barringtonSlotContinuation reversed (slotValue.testBit (2 * fuel))
        (slotValue.testBit (2 * fuel + 1)) onLeft onRight onInverseLeft
        onInverseRight).HoareTime
          (fun inp work out =>
            inp = inp₀ ∧
            (work layout.sourceIdx).head =
              (work₀ layout.sourceIdx).head + 2 * fuel ∧
            (work layout.sourceIdx).cells =
              (work₀ layout.sourceIdx).cells ∧
            (work layout.counterIdx).HasBinaryNat fuel ∧
            work layout.limitIdx = work₀ layout.limitIdx ∧
            (work layout.lowIdx).HasBinaryNat
              (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
            (work layout.highIdx).HasBinaryNat
              (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
            (∀ i, i ≠ layout.sourceIdx → i ≠ layout.counterIdx →
              i ≠ layout.limitIdx → i ≠ layout.lowIdx →
              i ≠ layout.highIdx → work i = work₀ i) ∧
            out = out₀)
          post selectedTime) :
    (barringtonInitialSlotBranchTM layout reversed onLeft onRight onInverseLeft
      onInverseRight).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        post (barringtonInitialSlotBranchTime fuel selectedTime) :=
  barringtonInitialSlotBranchTM_selected_hoareTime_internal layout reversed
    onLeft onRight onInverseLeft onInverseRight slotValue fuel inp₀ work₀ out₀
    hinput hslot hcounter hlimit hlowZero hhighZero hwork houtput hselected

/-- Initial positioning, exact bit capture, and two-step dispatch add no space
beyond the certified capture budget and the selected continuation's budget. -/
theorem barringtonInitialSlotBranchTM_selected_hoareTimeSpace
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n)
    (slotValue fuel inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : (work₀ layout.sourceIdx).HasBinaryNat slotValue)
    (hcounter : (work₀ layout.counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ layout.limitIdx).HasBinaryNat fuel)
    (hlowZero : (work₀ layout.lowIdx).HasBinaryNat 0)
    (hhighZero : (work₀ layout.highIdx).HasBinaryNat 0)
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
            (work layout.sourceIdx).head =
              (work₀ layout.sourceIdx).head + 2 * fuel ∧
            (work layout.sourceIdx).cells =
              (work₀ layout.sourceIdx).cells ∧
            (work layout.counterIdx).HasBinaryNat fuel ∧
            work layout.limitIdx = work₀ layout.limitIdx ∧
            (work layout.lowIdx).HasBinaryNat
              (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
            (work layout.highIdx).HasBinaryNat
              (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
            (∀ i, i ≠ layout.sourceIdx → i ≠ layout.counterIdx →
              i ≠ layout.limitIdx → i ≠ layout.lowIdx →
              i ≠ layout.highIdx → work i = work₀ i) ∧
            out = out₀)
          post selectedTime inputLength
          (positionCaptureSlotBitsSpace initialSpace fuel)) :
    (barringtonInitialSlotBranchTM layout reversed onLeft onRight onInverseLeft
      onInverseRight).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        post (barringtonInitialSlotBranchTime fuel selectedTime) inputLength
        (positionCaptureSlotBitsSpace initialSpace fuel) :=
  barringtonInitialSlotBranchTM_selected_hoareTimeSpace_internal layout
    reversed onLeft onRight onInverseLeft onInverseRight slotValue fuel
    inputLength initialSpace inp₀ work₀ out₀ hinput hslot hcounter hlimit
    hlowZero hhighZero hwork houtput hworkSpace hinputSpace hselected

/-- The initial slot controller selects the semantic child named by a
`BarringtonSlotCursor`; callers need not expose the underlying raw bits. -/
theorem barringtonInitialSlotBranchTM_cursor_hoareTimeSpace
    (layout : BarringtonSlotLayout n) (cursor : BarringtonSlotCursor)
    (onLeft onRight onInverseLeft onInverseRight : TM n)
    (fuel inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : (work₀ layout.sourceIdx).HasBinaryNat cursor.slot)
    (hcounter : (work₀ layout.counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ layout.limitIdx).HasBinaryNat fuel)
    (hlowZero : (work₀ layout.lowIdx).HasBinaryNat 0)
    (hhighZero : (work₀ layout.highIdx).HasBinaryNat 0)
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
            (work layout.sourceIdx).head =
              (work₀ layout.sourceIdx).head + 2 * fuel ∧
            (work layout.sourceIdx).cells =
              (work₀ layout.sourceIdx).cells ∧
            (work layout.counterIdx).HasBinaryNat fuel ∧
            work layout.limitIdx = work₀ layout.limitIdx ∧
            (work layout.lowIdx).HasBinaryNat
              (if cursor.slot.testBit (2 * fuel) then 1 else 0) ∧
            (work layout.highIdx).HasBinaryNat
              (if cursor.slot.testBit (2 * fuel + 1) then 1 else 0) ∧
            (∀ i, i ≠ layout.sourceIdx → i ≠ layout.counterIdx →
              i ≠ layout.limitIdx → i ≠ layout.lowIdx →
              i ≠ layout.highIdx → work i = work₀ i) ∧
            out = out₀)
          post selectedTime inputLength
          (positionCaptureSlotBitsSpace initialSpace fuel)) :
    (barringtonInitialSlotBranchTM layout cursor.reversed onLeft onRight
      onInverseLeft onInverseRight).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        post (barringtonInitialSlotBranchTime fuel selectedTime) inputLength
        (positionCaptureSlotBitsSpace initialSpace fuel) := by
  rw [← barringtonSlotContinuation_cursor cursor fuel onLeft onRight
    onInverseLeft onInverseRight] at hselected
  exact barringtonInitialSlotBranchTM_selected_hoareTimeSpace layout
    cursor.reversed onLeft onRight onInverseLeft onInverseRight cursor.slot fuel
    inputLength initialSpace inp₀ work₀ out₀ hinput hslot hcounter hlimit
    hlowZero hhighZero hwork houtput hworkSpace hinputSpace hselected

/-- Initial positioning and capture preserve one-way output behavior. -/
theorem positionCaptureSlotBitsTM_isTransducer
    (layout : BarringtonSlotLayout n) :
    (positionCaptureSlotBitsTM layout).IsTransducer :=
  positionCaptureSlotBitsTM_isTransducer_internal layout

/-- The complete initial slot branch is one-way on output when all four
continuations are. -/
theorem barringtonInitialSlotBranchTM_isTransducer
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    {onLeft onRight onInverseLeft onInverseRight : TM n}
    (hleft : onLeft.IsTransducer) (hright : onRight.IsTransducer)
    (hinverseLeft : onInverseLeft.IsTransducer)
    (hinverseRight : onInverseRight.IsTransducer) :
    (barringtonInitialSlotBranchTM layout reversed onLeft onRight onInverseLeft
      onInverseRight).IsTransducer :=
  barringtonInitialSlotBranchTM_isTransducer_internal layout reversed hleft
    hright hinverseLeft hinverseRight

end Machine

end BPCode

end Complexity
