/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotPosition.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotPosition.Internal

/-!
# Barrington slot positioning

This module exposes the certified constant-time movement bodies used by the
runtime binary-loop positioner for a preserved slot address.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- One positioning step moves only the designated slot-address head right. -/
theorem moveSlotRightTM_hoareTime
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (moveSlotRightTM sourceIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = moveSlotRightWork sourceIdx work₀ ∧ out = out₀)
      1 :=
  moveSlotRightTM_hoareTime_internal sourceIdx inp₀ work₀ out₀ hinput hwork
    houtput

/-- One positioning-loop body moves only the designated slot-address head two
cells right. -/
theorem advanceSlotDigitTM_hoareTime
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceNext : ((work₀ sourceIdx).move Dir3.right).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (advanceSlotDigitTM sourceIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx work₀) ∧
        out = out₀)
      2 :=
  advanceSlotDigitTM_hoareTime_internal sourceIdx inp₀ work₀ out₀ hinput
    hsourceNext hwork houtput

/-- The runtime binary loop places a canonical slot-address head on bit
`2 * fuel + 1`, preserving its cells and every unrelated tape. -/
theorem positionSlotTM_hoareTime
    (sourceIdx counterIdx limitIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (hcl : counterIdx ≠ limitIdx)
    (hsl : sourceIdx ≠ limitIdx)
    (slotValue fuel : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : (work₀ sourceIdx).HasBinaryNat slotValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat fuel)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (positionSlotTM sourceIdx counterIdx limitIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work sourceIdx).head = (work₀ sourceIdx).head + 2 * fuel + 1 ∧
        (work sourceIdx).cells = (work₀ sourceIdx).cells ∧
        (work counterIdx).HasBinaryNat fuel ∧
        work limitIdx = work₀ limitIdx ∧
        (∀ i, i ≠ sourceIdx → i ≠ counterIdx → i ≠ limitIdx →
          work i = work₀ i) ∧
        out = out₀)
      (positionSlotTime fuel) :=
  positionSlotTM_hoareTime_internal sourceIdx counterIdx limitIdx hsc hcl hsl
    slotValue fuel inp₀ work₀ out₀ hinput hslot hcounter hlimit hwork houtput

/-- Runtime positioning has a linear-in-`fuel` all-prefix space bound: the
main term is the `2 * fuel` source-head displacement, while binary-loop control
uses only the bit width of `fuel`. -/
theorem positionSlotTM_hoareTimeSpace
    (sourceIdx counterIdx limitIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (hcl : counterIdx ≠ limitIdx)
    (hsl : sourceIdx ≠ limitIdx)
    (slotValue fuel inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hslot : (work₀ sourceIdx).HasBinaryNat slotValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hlimit : (work₀ limitIdx).HasBinaryNat fuel)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (positionSlotTM sourceIdx counterIdx limitIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work sourceIdx).head = (work₀ sourceIdx).head + 2 * fuel + 1 ∧
        (work sourceIdx).cells = (work₀ sourceIdx).cells ∧
        (work counterIdx).HasBinaryNat fuel ∧
        work limitIdx = work₀ limitIdx ∧
        (∀ i, i ≠ sourceIdx → i ≠ counterIdx → i ≠ limitIdx →
          work i = work₀ i) ∧
        out = out₀)
      (positionSlotTime fuel) inputLength
      (positionSlotSpace initialSpace fuel) :=
  positionSlotTM_hoareTimeSpace_internal sourceIdx counterIdx limitIdx hsc hcl
    hsl slotValue fuel inputLength initialSpace inp₀ work₀ out₀ hinput hslot
    hcounter hlimit hwork houtput hworkSpace hinputSpace

/-- One rightward positioning step adds at most one cell to the starting
all-prefix auxiliary-space budget. -/
theorem moveSlotRightTM_hoareTimeSpace
    (sourceIdx : Fin n) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (moveSlotRightTM sourceIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } : Cfg n (moveSlotRightTM sourceIdx).Q)
        |>.WithinAuxSpace inputLength initialSpace) :
    (moveSlotRightTM sourceIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = moveSlotRightWork sourceIdx work₀ ∧ out = out₀)
      1 inputLength (initialSpace + 1) :=
  moveSlotRightTM_hoareTimeSpace_internal sourceIdx inputLength initialSpace
    inp₀ work₀ out₀ hinput hwork houtput hinitial

/-- One two-cell positioning body adds at most two cells to the starting
all-prefix auxiliary-space budget. -/
theorem advanceSlotDigitTM_hoareTimeSpace
    (sourceIdx : Fin n) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceNext : ((work₀ sourceIdx).move Dir3.right).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (advanceSlotDigitTM sourceIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } : Cfg n (advanceSlotDigitTM sourceIdx).Q)
        |>.WithinAuxSpace inputLength initialSpace) :
    (advanceSlotDigitTM sourceIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx work₀) ∧
        out = out₀)
      2 inputLength (initialSpace + 2) :=
  advanceSlotDigitTM_hoareTimeSpace_internal sourceIdx inputLength initialSpace
    inp₀ work₀ out₀ hinput hsourceNext hwork houtput hinitial

/-- The constant-time slot movement bodies never move output left. -/
theorem moveSlotRightTM_isTransducer (sourceIdx : Fin n) :
    (moveSlotRightTM sourceIdx).IsTransducer :=
  moveSlotRightTM_isTransducer_internal sourceIdx

/-- Advancing across one base-four digit never moves output left. -/
theorem advanceSlotDigitTM_isTransducer (sourceIdx : Fin n) :
    (advanceSlotDigitTM sourceIdx).IsTransducer :=
  advanceSlotDigitTM_isTransducer_internal sourceIdx

/-- The complete binary-loop slot positioner never moves output left. -/
theorem positionSlotTM_isTransducer
    (sourceIdx counterIdx limitIdx : Fin n) :
    (positionSlotTM sourceIdx counterIdx limitIdx).IsTransducer :=
  positionSlotTM_isTransducer_internal sourceIdx counterIdx limitIdx

end Machine

end BPCode

end Complexity
