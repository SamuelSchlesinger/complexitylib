/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotBranch.Defs
import Complexitylib.Circuits.BarringtonSlotQuery
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Barrington slot-bit branch machine -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

private theorem hasBinaryNat_bool_read_eq_one
    {tape : Tape} {bit : Bool}
    (hbit : tape.HasBinaryNat (if bit then 1 else 0)) :
    tape.read = Γ.one ↔ bit = true := by
  cases bit <;> rw [hbit.eq_init_move_right] <;>
    simp [Tape.read, Tape.init, Tape.move, Γ.ofBool]

private theorem branchWorkBitTM_selected_hoareTime
    (idx : Fin n) (bit : Bool) (onTrue onFalse : TM n)
    {pre post : TapePred n} {time : ℕ}
    (hinput : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start)
    (hwork : ∀ inp work out, pre inp work out →
      ∀ i, (work i).read ≠ Γ.start)
    (houtput : ∀ inp work out, pre inp work out →
      out.read ≠ Γ.start)
    (hbit : ∀ inp work out, pre inp work out →
      (work idx).HasBinaryNat (if bit then 1 else 0))
    (hselected : (if bit then onTrue else onFalse).HoareTime
      pre post time) :
    (branchWorkSymbolTM idx Γ.one onTrue onFalse).HoareTime
      pre post (time + 1) := by
  cases hvalue : bit
  · apply branchWorkSymbolTM_hoareTime_different
    · intro inp work out hpre hone
      have hfalse :=
        (hasBinaryNat_bool_read_eq_one (hbit inp work out hpre)).mp hone
      simp [hvalue] at hfalse
    · exact hinput
    · exact hwork
    · exact houtput
    · simpa [hvalue] using hselected
  · apply branchWorkSymbolTM_hoareTime_equal
    · intro inp work out hpre
      exact (hasBinaryNat_bool_read_eq_one
        (hbit inp work out hpre)).mpr hvalue
    · exact hinput
    · exact hwork
    · exact houtput
    · simpa [hvalue] using hselected

private theorem branchWorkBitTM_selected_hoareTimeSpace
    (idx : Fin n) (bit : Bool) (onTrue onFalse : TM n)
    {pre post : TapePred n} {time inputLength space : ℕ}
    (hinput : ∀ inp work out, pre inp work out →
      inp.read ≠ Γ.start)
    (hwork : ∀ inp work out, pre inp work out →
      ∀ i, (work i).read ≠ Γ.start)
    (houtput : ∀ inp work out, pre inp work out →
      out.read ≠ Γ.start)
    (hbit : ∀ inp work out, pre inp work out →
      (work idx).HasBinaryNat (if bit then 1 else 0))
    (hselected : (if bit then onTrue else onFalse).HoareTimeSpace
      pre post time inputLength space) :
    (branchWorkSymbolTM idx Γ.one onTrue onFalse).HoareTimeSpace
      pre post (time + 1) inputLength space := by
  cases hvalue : bit
  · apply branchWorkSymbolTM_hoareTimeSpace_different
    · intro inp work out hpre hone
      have hfalse :=
        (hasBinaryNat_bool_read_eq_one (hbit inp work out hpre)).mp hone
      simp [hvalue] at hfalse
    · exact hinput
    · exact hwork
    · exact houtput
    · simpa [hvalue] using hselected
  · apply branchWorkSymbolTM_hoareTimeSpace_equal
    · intro inp work out hpre
      exact (hasBinaryNat_bool_read_eq_one
        (hbit inp work out hpre)).mpr hvalue
    · exact hinput
    · exact hwork
    · exact houtput
    · simpa [hvalue] using hselected

theorem barringtonSlotContinuation_cursor_internal
    (cursor : BarringtonSlotCursor) (fuel : ℕ)
    (onLeft onRight onInverseLeft onInverseRight : TM n) :
    barringtonSlotContinuation cursor.reversed (cursor.rawLowBit fuel)
        (cursor.rawHighBit fuel) onLeft onRight onInverseLeft onInverseRight =
      if cursor.selectsInverse fuel then
        if cursor.selectsRight fuel then onInverseRight else onInverseLeft
      else if cursor.selectsRight fuel then onRight else onLeft := by
  rw [cursor.selectsRight_eq_rawLowBit fuel,
    cursor.selectsInverse_eq_rawHighBit fuel]
  rfl

theorem barringtonSlotBranchTM_selected_hoareTime_internal
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
      onInverseLeft onInverseRight).HoareTime pre post (time + 2) := by
  let inner (rawHigh : Bool) :=
    branchWorkSymbolTM lowIdx Γ.one
      (barringtonSlotContinuation reversed true rawHigh
        onLeft onRight onInverseLeft onInverseRight)
      (barringtonSlotContinuation reversed false rawHigh
        onLeft onRight onInverseLeft onInverseRight)
  have hinner : (inner high).HoareTime pre post (time + 1) := by
    apply branchWorkBitTM_selected_hoareTime lowIdx low
    · exact hinput
    · exact hwork
    · exact houtput
    · exact hlow
    · cases low <;> simpa [inner] using hselected
  have houter := branchWorkBitTM_selected_hoareTime highIdx high
    (inner true) (inner false) hinput hwork houtput hhigh (by
      cases high <;> simpa using hinner)
  simpa [barringtonSlotBranchTM, inner, Nat.add_assoc] using houter

theorem barringtonSlotBranchTM_selected_hoareTimeSpace_internal
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
        inputLength space := by
  let inner (rawHigh : Bool) :=
    branchWorkSymbolTM lowIdx Γ.one
      (barringtonSlotContinuation reversed true rawHigh
        onLeft onRight onInverseLeft onInverseRight)
      (barringtonSlotContinuation reversed false rawHigh
        onLeft onRight onInverseLeft onInverseRight)
  have hinner : (inner high).HoareTimeSpace pre post (time + 1)
      inputLength space := by
    apply branchWorkBitTM_selected_hoareTimeSpace lowIdx low
    · exact hinput
    · exact hwork
    · exact houtput
    · exact hlow
    · cases low <;> simpa [inner] using hselected
  have houter := branchWorkBitTM_selected_hoareTimeSpace highIdx high
    (inner true) (inner false) hinput hwork houtput hhigh (by
      cases high <;> simpa using hinner)
  simpa [barringtonSlotBranchTM, inner, Nat.add_assoc] using houter

private theorem barringtonSlotContinuation_isTransducer_internal
    (reversed low high : Bool)
    {onLeft onRight onInverseLeft onInverseRight : TM n}
    (hleft : onLeft.IsTransducer) (hright : onRight.IsTransducer)
    (hinverseLeft : onInverseLeft.IsTransducer)
    (hinverseRight : onInverseRight.IsTransducer) :
    (barringtonSlotContinuation reversed low high onLeft onRight
      onInverseLeft onInverseRight).IsTransducer := by
  cases reversed <;> cases low <;> cases high <;>
    simp [barringtonSlotContinuation] <;> assumption

theorem barringtonSlotBranchTM_isTransducer_internal
    (lowIdx highIdx : Fin n) (reversed : Bool)
    {onLeft onRight onInverseLeft onInverseRight : TM n}
    (hleft : onLeft.IsTransducer) (hright : onRight.IsTransducer)
    (hinverseLeft : onInverseLeft.IsTransducer)
    (hinverseRight : onInverseRight.IsTransducer) :
    (barringtonSlotBranchTM lowIdx highIdx reversed onLeft onRight
      onInverseLeft onInverseRight).IsTransducer := by
  apply IsTransducer.branchWorkSymbolTM
  · apply IsTransducer.branchWorkSymbolTM
    · exact barringtonSlotContinuation_isTransducer_internal
        reversed true true hleft hright hinverseLeft hinverseRight
    · exact barringtonSlotContinuation_isTransducer_internal
        reversed false true hleft hright hinverseLeft hinverseRight
  · apply IsTransducer.branchWorkSymbolTM
    · exact barringtonSlotContinuation_isTransducer_internal
        reversed true false hleft hright hinverseLeft hinverseRight
    · exact barringtonSlotContinuation_isTransducer_internal
        reversed false false hleft hright hinverseLeft hinverseRight

end Machine

end BPCode

end Complexity
