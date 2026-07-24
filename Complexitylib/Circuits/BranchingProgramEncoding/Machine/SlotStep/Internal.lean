/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotCapture
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotPosition
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotBranch
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotStep.Defs

/-!
# Barrington initial slot step -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

theorem positionCaptureSlotBitsTM_hoareTime_internal
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
      (positionCaptureSlotBitsTime fuel) := by
  have hrole : ∀ i j : Fin 5, i ≠ j → layout.roles i ≠ layout.roles j :=
    fun _ _ hij => layout.roles.injective.ne hij
  have hsc : layout.sourceIdx ≠ layout.counterIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.counterIdx
    exact hrole 0 1 (by decide)
  have hslimit : layout.sourceIdx ≠ layout.limitIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.limitIdx
    exact hrole 0 2 (by decide)
  have hslow : layout.sourceIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.lowIdx
    exact hrole 0 3 (by decide)
  have hshigh : layout.sourceIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.highIdx
    exact hrole 0 4 (by decide)
  have hclimit : layout.counterIdx ≠ layout.limitIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.limitIdx
    exact hrole 1 2 (by decide)
  have hclow : layout.counterIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.lowIdx
    exact hrole 1 3 (by decide)
  have hchigh : layout.counterIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.highIdx
    exact hrole 1 4 (by decide)
  have hlimitLow : layout.limitIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.limitIdx BarringtonSlotLayout.lowIdx
    exact hrole 2 3 (by decide)
  have hlimitHigh : layout.limitIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.limitIdx BarringtonSlotLayout.highIdx
    exact hrole 2 4 (by decide)
  have hlowHigh : layout.lowIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.lowIdx BarringtonSlotLayout.highIdx
    exact hrole 3 4 (by decide)
  let positioned : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work layout.sourceIdx).head =
      (work₀ layout.sourceIdx).head + 2 * fuel + 1 ∧
    (work layout.sourceIdx).cells = (work₀ layout.sourceIdx).cells ∧
    (work layout.counterIdx).HasBinaryNat fuel ∧
    work layout.limitIdx = work₀ layout.limitIdx ∧
    (∀ i, i ≠ layout.sourceIdx → i ≠ layout.counterIdx →
      i ≠ layout.limitIdx → work i = work₀ i) ∧
    out = out₀
  have hposition := positionSlotTM_hoareTime layout.sourceIdx
    layout.counterIdx layout.limitIdx hsc hclimit hslimit slotValue fuel inp₀
    work₀ out₀ hinput hslot hcounter hlimit hwork houtput
  have hpositionedReads : ∀ inp work out, positioned inp work out →
      ∀ i, (work i).read ≠ Γ.start := by
    intro inp work out hpos i
    rcases hpos with ⟨-, hsourceHead, hsourceCells, hcounterFuel,
      hlimitEq, hother, -⟩
    by_cases his : i = layout.sourceIdx
    · subst i
      rw [Tape.read, hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work layout.sourceIdx).head) (by rw [hsourceHead, hslot.2.1]; omega)
    by_cases hic : i = layout.counterIdx
    · subst i
      exact hcounterFuel.2.hasBinarySuffix.read_ne_start
    by_cases hil : i = layout.limitIdx
    · subst i
      rw [hlimitEq]
      exact hwork layout.limitIdx
    · rw [hother i his hic hil]
      exact hwork i
  have hcapture :
      (captureSlotBitsTM layout.sourceIdx layout.lowIdx layout.highIdx)
        |>.HoareTime positioned
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
          3 := by
    intro inp work out hpos
    rcases hpos with ⟨hinp, hsourceHead, hsourceCells, hcounterFuel,
      hlimitEq, hother, hout⟩
    have hlowEq : work layout.lowIdx = work₀ layout.lowIdx :=
      hother layout.lowIdx hslow.symm hclow.symm hlimitLow.symm
    have hhighEq : work layout.highIdx = work₀ layout.highIdx :=
      hother layout.highIdx hshigh.symm hchigh.symm hlimitHigh.symm
    have hsourceHighRead : (work layout.sourceIdx).read ≠ Γ.start :=
      hpositionedReads inp work out
        ⟨hinp, hsourceHead, hsourceCells, hcounterFuel, hlimitEq, hother, hout⟩
        layout.sourceIdx
    have hsourceLowRead :
        ((work layout.sourceIdx).move Dir3.left).read ≠ Γ.start := by
      simp only [Tape.read, Tape.move]
      rw [hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work layout.sourceIdx).head - 1)
        (by rw [hsourceHead, hslot.2.1]; omega)
    have hrun := captureSlotBitsTM_hoareTime layout.sourceIdx layout.lowIdx
      layout.highIdx hslow hshigh hlowHigh inp work out
      (by rw [hinp]; exact hinput) hsourceHighRead hsourceLowRead
      (hpositionedReads inp work out
        ⟨hinp, hsourceHead, hsourceCells, hcounterFuel, hlimitEq, hother, hout⟩)
      (by rw [hlowEq]; exact hlowZero) (by rw [hhighEq]; exact hhighZero)
      (by rw [hout]; exact houtput)
    obtain ⟨c, time, htime, hreach, hhalt, hpost⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    rcases hpost with ⟨hfinalInput, hfinalSource, hfinalLow, hfinalHigh,
      hfinalOther, hfinalOutput⟩
    have hhighBit : slotBitAtHead (work layout.sourceIdx) =
        slotValue.testBit (2 * fuel + 1) := by
      apply slotBitAtHead_eq_testBit_of_cells
        (work layout.sourceIdx) (work₀ layout.sourceIdx) slotValue
          (2 * fuel + 1) hslot hsourceCells
      rw [hsourceHead, hslot.2.1]
      omega
    have hlowBit : slotBitAtHead ((work layout.sourceIdx).move Dir3.left) =
        slotValue.testBit (2 * fuel) := by
      apply slotBitAtHead_eq_testBit_of_cells
        ((work layout.sourceIdx).move Dir3.left) (work₀ layout.sourceIdx)
          slotValue (2 * fuel) hslot
      · exact hsourceCells
      · simp only [Tape.move]
        rw [hsourceHead, hslot.2.1]
        omega
    refine ⟨c, time, htime, hreach, hhalt, hfinalInput.trans hinp, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, hfinalOutput.trans hout⟩
    · rw [hfinalSource]
      simp only [Tape.move]
      rw [hsourceHead, hslot.2.1]
      omega
    · rw [hfinalSource, Tape.move_cells]
      exact hsourceCells
    · rw [hfinalOther layout.counterIdx hsc.symm hclow hchigh]
      exact hcounterFuel
    · rw [hfinalOther layout.limitIdx hslimit.symm hlimitLow hlimitHigh]
      exact hlimitEq
    · simpa [hlowBit] using hfinalLow
    · simpa [hhighBit] using hfinalHigh
    · intro i his hic hil hilow hihigh
      rw [hfinalOther i his hilow hihigh]
      exact hother i his hic hil
  have htransition : ∀ inp work out, positioned inp work out →
      positioned (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hpos
    rcases hpos with ⟨hinp, hsourceHead, hsourceCells, hcounterFuel,
      hlimitEq, hother, hout⟩
    have hpos' : positioned inp work out :=
      ⟨hinp, hsourceHead, hsourceCells, hcounterFuel, hlimitEq, hother, hout⟩
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      (inp := inp) (work := work) (out := out)
      (by simpa [hinp] using hinput) (hpositionedReads inp work out hpos')
      (by simpa [hout] using houtput)
    rw [hi, hw, ho]
    exact hpos'
  simpa [positionCaptureSlotBitsTM, positionCaptureSlotBitsTime, positioned]
    using TM.seqTM_hoareTime _ _ hposition htransition hcapture

theorem positionCaptureSlotBitsTM_hoareTimeSpace_internal
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
      (positionCaptureSlotBitsSpace initialSpace fuel) := by
  have hrole : ∀ i j : Fin 5, i ≠ j → layout.roles i ≠ layout.roles j :=
    fun _ _ hij => layout.roles.injective.ne hij
  have hsc : layout.sourceIdx ≠ layout.counterIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.counterIdx
    exact hrole 0 1 (by decide)
  have hslimit : layout.sourceIdx ≠ layout.limitIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.limitIdx
    exact hrole 0 2 (by decide)
  have hslow : layout.sourceIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.lowIdx
    exact hrole 0 3 (by decide)
  have hshigh : layout.sourceIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.highIdx
    exact hrole 0 4 (by decide)
  have hclimit : layout.counterIdx ≠ layout.limitIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.limitIdx
    exact hrole 1 2 (by decide)
  have hclow : layout.counterIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.lowIdx
    exact hrole 1 3 (by decide)
  have hchigh : layout.counterIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.highIdx
    exact hrole 1 4 (by decide)
  have hlimitLow : layout.limitIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.limitIdx BarringtonSlotLayout.lowIdx
    exact hrole 2 3 (by decide)
  have hlimitHigh : layout.limitIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.limitIdx BarringtonSlotLayout.highIdx
    exact hrole 2 4 (by decide)
  have hlowHigh : layout.lowIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.lowIdx BarringtonSlotLayout.highIdx
    exact hrole 3 4 (by decide)
  let positioned : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work layout.sourceIdx).head =
      (work₀ layout.sourceIdx).head + 2 * fuel + 1 ∧
    (work layout.sourceIdx).cells = (work₀ layout.sourceIdx).cells ∧
    (work layout.counterIdx).HasBinaryNat fuel ∧
    work layout.limitIdx = work₀ layout.limitIdx ∧
    (∀ i, i ≠ layout.sourceIdx → i ≠ layout.counterIdx →
      i ≠ layout.limitIdx → work i = work₀ i) ∧
    out = out₀
  have hpositionedReads : ∀ inp work out, positioned inp work out →
      ∀ i, (work i).read ≠ Γ.start := by
    intro inp work out hpos i
    rcases hpos with ⟨-, hsourceHead, hsourceCells, hcounterFuel,
      hlimitEq, hother, -⟩
    by_cases his : i = layout.sourceIdx
    · subst i
      rw [Tape.read, hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work layout.sourceIdx).head) (by rw [hsourceHead, hslot.2.1]; omega)
    by_cases hic : i = layout.counterIdx
    · subst i
      exact hcounterFuel.2.hasBinarySuffix.read_ne_start
    by_cases hil : i = layout.limitIdx
    · subst i
      rw [hlimitEq]
      exact hwork layout.limitIdx
    · rw [hother i his hic hil]
      exact hwork i
  have hposition := positionSlotTM_hoareTimeSpace layout.sourceIdx
    layout.counterIdx layout.limitIdx hsc hclimit hslimit slotValue fuel
    inputLength initialSpace inp₀ work₀ out₀ hinput hslot hcounter hlimit hwork
    houtput hworkSpace hinputSpace
  have hcaptureTime :
      (captureSlotBitsTM layout.sourceIdx layout.lowIdx layout.highIdx)
        |>.HoareTime positioned (fun _ _ _ => True) 3 := by
    intro inp work out hpos
    rcases hpos with ⟨hinp, hsourceHead, hsourceCells, hcounterFuel,
      hlimitEq, hother, hout⟩
    have hlowEq : work layout.lowIdx = work₀ layout.lowIdx :=
      hother layout.lowIdx hslow.symm hclow.symm hlimitLow.symm
    have hhighEq : work layout.highIdx = work₀ layout.highIdx :=
      hother layout.highIdx hshigh.symm hchigh.symm hlimitHigh.symm
    have hsourceLowRead :
        ((work layout.sourceIdx).move Dir3.left).read ≠ Γ.start := by
      simp only [Tape.read, Tape.move]
      rw [hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work layout.sourceIdx).head - 1)
        (by rw [hsourceHead, hslot.2.1]; omega)
    have hrun := captureSlotBitsTM_hoareTime layout.sourceIdx layout.lowIdx
      layout.highIdx hslow hshigh hlowHigh inp work out
      (by rw [hinp]; exact hinput)
      (hpositionedReads inp work out
        ⟨hinp, hsourceHead, hsourceCells, hcounterFuel, hlimitEq, hother, hout⟩
        layout.sourceIdx)
      hsourceLowRead
      (hpositionedReads inp work out
        ⟨hinp, hsourceHead, hsourceCells, hcounterFuel, hlimitEq, hother, hout⟩)
      (by rw [hlowEq]; exact hlowZero) (by rw [hhighEq]; exact hhighZero)
      (by rw [hout]; exact houtput)
    obtain ⟨c, time, htime, hreach, hhalt, -⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨c, time, htime, hreach, hhalt, trivial⟩
  have hpositionedWithin : ∀ inp work out, positioned inp work out →
      ({ state :=
          (captureSlotBitsTM layout.sourceIdx layout.lowIdx layout.highIdx).qstart,
         input := inp,
         work := work,
         output := out } :
        Cfg n (captureSlotBitsTM layout.sourceIdx layout.lowIdx
          layout.highIdx).Q).WithinAuxSpace inputLength
            (positionSlotSpace initialSpace fuel) := by
    intro inp work out hpos
    rcases hpos with ⟨hinp, hsourceHead, -, hcounterFuel, hlimitEq, hother, -⟩
    constructor
    · intro i
      by_cases his : i = layout.sourceIdx
      · subst i
        change (work layout.sourceIdx).head ≤ positionSlotSpace initialSpace fuel
        have hsourceInitial := hworkSpace layout.sourceIdx
        rw [hsourceHead]
        simp [positionSlotSpace]
        omega
      by_cases hic : i = layout.counterIdx
      · subst i
        change (work layout.counterIdx).head ≤ positionSlotSpace initialSpace fuel
        rw [hcounterFuel.2.1]
        have hone : 1 ≤ initialSpace := by
          rw [← hcounter.2.1]
          exact hworkSpace layout.counterIdx
        simp [positionSlotSpace]
      by_cases hil : i = layout.limitIdx
      · subst i
        change (work layout.limitIdx).head ≤ positionSlotSpace initialSpace fuel
        rw [hlimitEq]
        exact le_trans (hworkSpace layout.limitIdx) (by
          simp [positionSlotSpace]; omega)
      · change (work i).head ≤ positionSlotSpace initialSpace fuel
        rw [hother i his hic hil]
        exact le_trans (hworkSpace i) (by simp [positionSlotSpace]; omega)
    · change inp.head ≤ inputLength + positionSlotSpace initialSpace fuel + 1
      rw [hinp]
      exact le_trans hinputSpace (by simp [positionSlotSpace]; omega)
  have hcaptureSpace := hcaptureTime.toHoareTimeSpace hpositionedWithin
  have htransition : ∀ inp work out, positioned inp work out →
      positioned (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hpos
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      (inp := inp) (work := work) (out := out)
      (by rw [hpos.1]; exact hinput) (hpositionedReads inp work out hpos)
      (by rw [hpos.2.2.2.2.2.2]; exact houtput)
    rw [hi, hw, ho]
    exact hpos
  have hseq := TM.seqTM_hoareTimeSpace _ _ hposition htransition hcaptureSpace
  have htime := positionCaptureSlotBitsTM_hoareTime_internal layout slotValue
    fuel inp₀ work₀ out₀ hinput hslot hcounter hlimit hlowZero hhighZero hwork
    houtput
  refine htime.and_hoareSpace ?_
  simpa [positionCaptureSlotBitsTM, positionCaptureSlotBitsSpace, positioned]
    using hseq.2

theorem barringtonInitialSlotBranchTM_selected_hoareTime_internal
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
        post (barringtonInitialSlotBranchTime fuel selectedTime) := by
  have hrole : ∀ i j : Fin 5, i ≠ j → layout.roles i ≠ layout.roles j :=
    fun _ _ hij => layout.roles.injective.ne hij
  have hsc : layout.sourceIdx ≠ layout.counterIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.counterIdx
    exact hrole 0 1 (by decide)
  have hslimit : layout.sourceIdx ≠ layout.limitIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.limitIdx
    exact hrole 0 2 (by decide)
  have hslow : layout.sourceIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.lowIdx
    exact hrole 0 3 (by decide)
  have hshigh : layout.sourceIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.highIdx
    exact hrole 0 4 (by decide)
  have hclimit : layout.counterIdx ≠ layout.limitIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.limitIdx
    exact hrole 1 2 (by decide)
  have hclow : layout.counterIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.lowIdx
    exact hrole 1 3 (by decide)
  have hchigh : layout.counterIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.counterIdx BarringtonSlotLayout.highIdx
    exact hrole 1 4 (by decide)
  have hlimitLow : layout.limitIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.limitIdx BarringtonSlotLayout.lowIdx
    exact hrole 2 3 (by decide)
  have hlimitHigh : layout.limitIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.limitIdx BarringtonSlotLayout.highIdx
    exact hrole 2 4 (by decide)
  let captured : TapePred n := fun inp work out =>
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
    out = out₀
  have hcapture := positionCaptureSlotBitsTM_hoareTime_internal layout
    slotValue fuel inp₀ work₀ out₀ hinput hslot hcounter hlimit hlowZero
    hhighZero hwork houtput
  have hcapturedReads : ∀ inp work out, captured inp work out →
      ∀ i, (work i).read ≠ Γ.start := by
    intro inp work out hcap i
    rcases hcap with ⟨-, hsourceHead, hsourceCells, hcounterFuel,
      hlimitEq, hlow, hhigh, hother, -⟩
    by_cases his : i = layout.sourceIdx
    · subst i
      rw [Tape.read, hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work layout.sourceIdx).head) (by rw [hsourceHead, hslot.2.1]; omega)
    by_cases hic : i = layout.counterIdx
    · subst i
      exact hcounterFuel.2.hasBinarySuffix.read_ne_start
    by_cases hil : i = layout.limitIdx
    · subst i
      rw [hlimitEq]
      exact hwork layout.limitIdx
    by_cases hilow : i = layout.lowIdx
    · subst i
      exact hlow.2.hasBinarySuffix.read_ne_start
    by_cases hihigh : i = layout.highIdx
    · subst i
      exact hhigh.2.hasBinarySuffix.read_ne_start
    · rw [hother i his hic hil hilow hihigh]
      exact hwork i
  have hbranch := barringtonSlotBranchTM_selected_hoareTime layout.lowIdx
    layout.highIdx reversed (slotValue.testBit (2 * fuel))
    (slotValue.testBit (2 * fuel + 1)) onLeft onRight onInverseLeft
    onInverseRight
    (fun inp work out hcap => by rw [hcap.1]; exact hinput)
    hcapturedReads
    (fun inp work out hcap => by rw [hcap.2.2.2.2.2.2.2.2]; exact houtput)
    (fun _ _ _ hcap => hcap.2.2.2.2.2.1)
    (fun _ _ _ hcap => hcap.2.2.2.2.2.2.1)
    hselected
  have htransition : ∀ inp work out, captured inp work out →
      captured (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hcap
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      (inp := inp) (work := work) (out := out)
      (by rw [hcap.1]; exact hinput) (hcapturedReads inp work out hcap)
      (by rw [hcap.2.2.2.2.2.2.2.2]; exact houtput)
    rw [hi, hw, ho]
    exact hcap
  simpa [barringtonInitialSlotBranchTM, barringtonInitialSlotBranchTime,
    captured] using TM.seqTM_hoareTime _ _ hcapture htransition hbranch

theorem barringtonInitialSlotBranchTM_selected_hoareTimeSpace_internal
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
        (positionCaptureSlotBitsSpace initialSpace fuel) := by
  let captured : TapePred n := fun inp work out =>
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
    out = out₀
  have hcapture := positionCaptureSlotBitsTM_hoareTimeSpace_internal layout
    slotValue fuel inputLength initialSpace inp₀ work₀ out₀ hinput hslot
    hcounter hlimit hlowZero hhighZero hwork houtput hworkSpace hinputSpace
  have hcapturedReads : ∀ inp work out, captured inp work out →
      ∀ i, (work i).read ≠ Γ.start := by
    intro inp work out hcap i
    rcases hcap with ⟨-, hsourceHead, hsourceCells, hcounterFuel,
      hlimitEq, hlow, hhigh, hother, -⟩
    by_cases his : i = layout.sourceIdx
    · subst i
      rw [Tape.read, hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work layout.sourceIdx).head) (by rw [hsourceHead, hslot.2.1]; omega)
    by_cases hic : i = layout.counterIdx
    · subst i
      exact hcounterFuel.2.hasBinarySuffix.read_ne_start
    by_cases hil : i = layout.limitIdx
    · subst i
      rw [hlimitEq]
      exact hwork layout.limitIdx
    by_cases hilow : i = layout.lowIdx
    · subst i
      exact hlow.2.hasBinarySuffix.read_ne_start
    by_cases hihigh : i = layout.highIdx
    · subst i
      exact hhigh.2.hasBinarySuffix.read_ne_start
    · rw [hother i his hic hil hilow hihigh]
      exact hwork i
  have hbranch := barringtonSlotBranchTM_selected_hoareTimeSpace layout.lowIdx
    layout.highIdx reversed (slotValue.testBit (2 * fuel))
    (slotValue.testBit (2 * fuel + 1)) onLeft onRight onInverseLeft
    onInverseRight
    (fun inp work out hcap => by rw [hcap.1]; exact hinput)
    hcapturedReads
    (fun inp work out hcap => by rw [hcap.2.2.2.2.2.2.2.2]; exact houtput)
    (fun _ _ _ hcap => hcap.2.2.2.2.2.1)
    (fun _ _ _ hcap => hcap.2.2.2.2.2.2.1)
    hselected
  have htransition : ∀ inp work out, captured inp work out →
      captured (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hcap
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      (inp := inp) (work := work) (out := out)
      (by rw [hcap.1]; exact hinput) (hcapturedReads inp work out hcap)
      (by rw [hcap.2.2.2.2.2.2.2.2]; exact houtput)
    rw [hi, hw, ho]
    exact hcap
  simpa [barringtonInitialSlotBranchTM, barringtonInitialSlotBranchTime,
    captured] using TM.seqTM_hoareTimeSpace _ _ hcapture htransition hbranch

theorem positionCaptureSlotBitsTM_isTransducer_internal
    (layout : BarringtonSlotLayout n) :
    (positionCaptureSlotBitsTM layout).IsTransducer := by
  exact (positionSlotTM_isTransducer layout.sourceIdx layout.counterIdx
    layout.limitIdx).seqTM
      (captureSlotBitsTM_isTransducer layout.sourceIdx layout.lowIdx
        layout.highIdx)

theorem barringtonInitialSlotBranchTM_isTransducer_internal
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    {onLeft onRight onInverseLeft onInverseRight : TM n}
    (hleft : onLeft.IsTransducer) (hright : onRight.IsTransducer)
    (hinverseLeft : onInverseLeft.IsTransducer)
    (hinverseRight : onInverseRight.IsTransducer) :
    (barringtonInitialSlotBranchTM layout reversed onLeft onRight onInverseLeft
      onInverseRight).IsTransducer := by
  exact (positionCaptureSlotBitsTM_isTransducer_internal layout).seqTM
    (barringtonSlotBranchTM_isTransducer layout.lowIdx layout.highIdx reversed
      hleft hright hinverseLeft hinverseRight)

end Machine

end BPCode

end Complexity
