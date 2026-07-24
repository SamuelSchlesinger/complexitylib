/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotBranch.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotBranch.Internal

/-!
# Barrington slot-bit branch machine

This module exposes the concrete four-way continuation dispatcher used after
capturing the two binary address bits of one stack-free slot-cursor step.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- The raw-bit continuation selected by the concrete dispatcher agrees with
the semantic right-child and inverse-block decisions of the slot cursor. -/
theorem barringtonSlotContinuation_cursor
    (cursor : BarringtonSlotCursor) (fuel : ℕ)
    (onLeft onRight onInverseLeft onInverseRight : TM n) :
    barringtonSlotContinuation cursor.reversed (cursor.rawLowBit fuel)
        (cursor.rawHighBit fuel) onLeft onRight onInverseLeft onInverseRight =
      if cursor.selectsInverse fuel then
        if cursor.selectsRight fuel then onInverseRight else onInverseLeft
      else if cursor.selectsRight fuel then onRight else onLeft :=
  barringtonSlotContinuation_cursor_internal cursor fuel onLeft onRight
    onInverseLeft onInverseRight

/-- Two captured raw address bits and one finite reflection flag select exactly
one Barrington child continuation in two tape-preserving dispatch steps. -/
theorem barringtonSlotBranchTM_selected_hoareTime
    (lowIdx highIdx : Fin n)
    (reversed low high : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n)
    {pre post : TapePred n} {time : ℕ}
    (hinput : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start)
    (hwork : ∀ inp work out, pre inp work out →
      ∀ i, (work i).read ≠ Γ.start)
    (houtput : ∀ inp work out, pre inp work out →
      out.read ≠ Γ.start)
    (hlow : ∀ inp work out, pre inp work out →
      (work lowIdx).HasBinaryNat (if low then 1 else 0))
    (hhigh : ∀ inp work out, pre inp work out →
      (work highIdx).HasBinaryNat (if high then 1 else 0))
    (hselected :
      (barringtonSlotContinuation reversed low high onLeft onRight
        onInverseLeft onInverseRight).HoareTime pre post time) :
    (barringtonSlotBranchTM lowIdx highIdx reversed onLeft onRight
      onInverseLeft onInverseRight).HoareTime pre post (time + 2) :=
  barringtonSlotBranchTM_selected_hoareTime_internal lowIdx highIdx reversed
    low high onLeft onRight onInverseLeft onInverseRight hinput hwork houtput
    hlow hhigh hselected

/-- The selected two-bit dispatch adds exactly two transitions and no auxiliary
space beyond the chosen continuation's all-prefix budget. -/
theorem barringtonSlotBranchTM_selected_hoareTimeSpace
    (lowIdx highIdx : Fin n)
    (reversed low high : Bool)
    (onLeft onRight onInverseLeft onInverseRight : TM n)
    {pre post : TapePred n} {time inputLength space : ℕ}
    (hinput : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start)
    (hwork : ∀ inp work out, pre inp work out →
      ∀ i, (work i).read ≠ Γ.start)
    (houtput : ∀ inp work out, pre inp work out →
      out.read ≠ Γ.start)
    (hlow : ∀ inp work out, pre inp work out →
      (work lowIdx).HasBinaryNat (if low then 1 else 0))
    (hhigh : ∀ inp work out, pre inp work out →
      (work highIdx).HasBinaryNat (if high then 1 else 0))
    (hselected :
      (barringtonSlotContinuation reversed low high onLeft onRight
        onInverseLeft onInverseRight).HoareTimeSpace pre post time
          inputLength space) :
    (barringtonSlotBranchTM lowIdx highIdx reversed onLeft onRight
      onInverseLeft onInverseRight).HoareTimeSpace pre post (time + 2)
        inputLength space :=
  barringtonSlotBranchTM_selected_hoareTimeSpace_internal lowIdx highIdx
    reversed low high onLeft onRight onInverseLeft onInverseRight hinput
    hwork houtput hlow hhigh hselected

/-- The two-bit Barrington dispatcher preserves one-way output behavior when
all four child continuations do. -/
theorem barringtonSlotBranchTM_isTransducer
    (lowIdx highIdx : Fin n) (reversed : Bool)
    {onLeft onRight onInverseLeft onInverseRight : TM n}
    (hleft : onLeft.IsTransducer) (hright : onRight.IsTransducer)
    (hinverseLeft : onInverseLeft.IsTransducer)
    (hinverseRight : onInverseRight.IsTransducer) :
    (barringtonSlotBranchTM lowIdx highIdx reversed onLeft onRight
      onInverseLeft onInverseRight).IsTransducer :=
  barringtonSlotBranchTM_isTransducer_internal lowIdx highIdx reversed hleft
    hright hinverseLeft hinverseRight

end Machine

end BPCode

end Complexity
