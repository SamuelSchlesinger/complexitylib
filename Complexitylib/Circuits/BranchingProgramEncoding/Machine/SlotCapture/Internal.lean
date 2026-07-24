/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotCapture.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Mathlib.Data.Nat.Bitwise

/-!
# Barrington slot-bit capture -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

theorem slotBitAtHead_eq_testBit_of_cells_internal
    (tape original : Tape) (value offset : ℕ)
    (hvalue : original.HasBinaryNat value)
    (hcells : tape.cells = original.cells)
    (hhead : tape.head = offset + 1) :
    slotBitAtHead tape = value.testBit offset := by
  rw [slotBitAtHead, Nat.testBit_eq_inth]
  by_cases hi : offset < value.bits.length
  · rw [Tape.read, hhead, hcells, hvalue.2.2.1 offset hi,
      List.getI_eq_getElem (l := value.bits) hi]
    cases value.bits[offset] <;> rfl
  · have hle : value.bits.length ≤ offset := Nat.le_of_not_gt hi
    rw [Tape.read, hhead, hcells, hvalue.2.2.2 offset hle,
      List.getI_eq_default (l := value.bits) hle]
    rfl

theorem slotBitAtHead_eq_testBit_internal
    (tape : Tape) (value offset : ℕ)
    (hvalue : tape.HasBinaryNat value)
    (hhead : tape.head = offset + 1) :
    slotBitAtHead tape = value.testBit offset :=
  slotBitAtHead_eq_testBit_of_cells_internal tape tape value offset hvalue rfl
    hhead

private theorem captureSlotBitTM_step
    (sourceIdx targetIdx : Fin n) (hne : sourceIdx ≠ targetIdx)
    (moveLeft : Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsource : (work₀ sourceIdx).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (captureSlotBitTM sourceIdx targetIdx moveLeft).step
      { state := (captureSlotBitTM sourceIdx targetIdx moveLeft).qstart
        input := inp₀
        work := work₀
        output := out₀ } =
      some
        { state := (captureSlotBitTM sourceIdx targetIdx moveLeft).qhalt
          input := inp₀
          work := captureSlotBitWork sourceIdx targetIdx moveLeft work₀
          output := out₀ } := by
  rw [TM.step, if_neg (by simp [captureSlotBitTM])]
  simp only [captureSlotBitTM, hsource, ↓reduceIte]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · dsimp only
    simp [TM.idleDir, hinput, Tape.move]
  · dsimp only
    funext i
    by_cases his : i = sourceIdx
    · subst i
      cases moveLeft
      · simp [captureSlotBitWork, hne, TM.idleDir, hsource]
      · simp only [Bool.true_and, if_pos, captureSlotBitWork,
          if_neg hne]
        simp
    · by_cases hit : i = targetIdx
      · subst i
        simp [captureSlotBitWork, his, slotBitAtHead, TM.idleDir,
          hwork targetIdx]
      · simp only [captureSlotBitWork, if_neg his, if_neg hit]
        simp [his, TM.idleDir, hwork i, Tape.move]
  · dsimp only
    simpa [TM.idleDir, houtput, Tape.move] using
      TM.writeAndMove_readBack out₀ houtput Dir3.stay

theorem captureSlotBitWork_source_internal
    (sourceIdx targetIdx : Fin n)
    (moveLeft : Bool) (work : Fin n → Tape)
    (hsource : (work sourceIdx).read ≠ Γ.start) :
    captureSlotBitWork sourceIdx targetIdx moveLeft work sourceIdx =
      if moveLeft then (work sourceIdx).move Dir3.left
      else work sourceIdx := by
  rw [captureSlotBitWork, if_pos rfl]
  cases moveLeft
  · simp only [Bool.false_eq_true, if_false]
    exact TM.writeAndMove_readBack (work sourceIdx) hsource Dir3.stay
  · simp only [if_true]
    exact TM.writeAndMove_readBack (work sourceIdx) hsource Dir3.left

theorem captureSlotBitWork_other_internal
    (sourceIdx targetIdx : Fin n) (moveLeft : Bool)
    (work : Fin n → Tape) (i : Fin n)
    (his : i ≠ sourceIdx) (hit : i ≠ targetIdx)
    (hread : (work i).read ≠ Γ.start) :
    captureSlotBitWork sourceIdx targetIdx moveLeft work i = work i := by
  simpa [captureSlotBitWork, his, hit, TM.idleDir, hread, Tape.move] using
    TM.writeAndMove_readBack (work i) hread Dir3.stay

theorem captureSlotBitWork_target_internal
    (sourceIdx targetIdx : Fin n) (hne : sourceIdx ≠ targetIdx)
    (moveLeft : Bool) (work : Fin n → Tape)
    (hzero : (work targetIdx).HasBinaryNat 0) :
    (captureSlotBitWork sourceIdx targetIdx moveLeft work targetIdx)
        |>.HasBinaryNat
          (if slotBitAtHead (work sourceIdx) then 1 else 0) := by
  simp only [captureSlotBitWork, if_neg hne.symm, if_pos]
  rw [hzero.eq_init_move_right]
  cases hbit : slotBitAtHead (work sourceIdx) <;>
    simp [slotBitWrite, Tape.writeAndMove, Tape.write, Tape.move,
      Tape.init, Γ.ofBool, Tape.HasBinaryNat, Tape.HasBinaryString]
  · intro i
    by_cases hi : i = 0
    · subst i
      simp
    · rw [Function.update_of_ne (by omega)]
      simp [hi]
  · intro i hi
    rw [Function.update_of_ne (by omega)]
    simp

theorem captureSlotBitTM_hoareTime_frame_internal
    (sourceIdx targetIdx : Fin n) (hne : sourceIdx ≠ targetIdx)
    (moveLeft : Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsource : (work₀ sourceIdx).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (captureSlotBitTM sourceIdx targetIdx moveLeft).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = captureSlotBitWork sourceIdx targetIdx moveLeft work₀ ∧
        out = out₀)
      1 := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  rw [hinp, hworkEq, hout]
  have hstep := captureSlotBitTM_step sourceIdx targetIdx hne moveLeft
    inp₀ work₀ out₀ hinput hsource hwork houtput
  exact ⟨_, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

theorem captureSlotBitTM_hoareTime_internal
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
      1 := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  rw [hinp, hworkEq, hout]
  have hstep := captureSlotBitTM_step sourceIdx targetIdx hne moveLeft
    inp₀ work₀ out₀ hinput hsource hwork houtput
  refine ⟨_, 1, le_rfl, .step hstep .zero, rfl, ?_⟩
  refine ⟨rfl,
    captureSlotBitWork_source_internal sourceIdx targetIdx moveLeft work₀
      hsource,
    captureSlotBitWork_target_internal sourceIdx targetIdx hne moveLeft work₀
      hzero,
    ?_, rfl⟩
  intro i his hit
  exact captureSlotBitWork_other_internal sourceIdx targetIdx moveLeft work₀ i
    his hit (hwork i)

theorem captureSlotBitTM_hoareTimeSpace_internal
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
      1 inputLength (initialSpace + 1) := by
  apply (captureSlotBitTM_hoareTime_internal sourceIdx targetIdx hne moveLeft
    inp₀ work₀ out₀ hinput hsource hwork hzero houtput).toHoareTimeSpace
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  subst inp
  subst work
  subst out
  exact hinitial

theorem captureSlotBitsTM_hoareTime_frame_internal
    (sourceIdx lowIdx highIdx : Fin n)
    (hsl : sourceIdx ≠ lowIdx) (hsh : sourceIdx ≠ highIdx)
    (hlh : lowIdx ≠ highIdx)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceHigh : (work₀ sourceIdx).read ≠ Γ.start)
    (hsourceLow : ((work₀ sourceIdx).move Dir3.left).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (hhighZero : (work₀ highIdx).HasBinaryNat 0)
    (houtput : out₀.read ≠ Γ.start) :
    (captureSlotBitsTM sourceIdx lowIdx highIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = captureSlotBitsWork sourceIdx lowIdx highIdx work₀ ∧
        out = out₀)
      3 := by
  let work₁ := captureSlotBitWork sourceIdx highIdx true work₀
  have hsource₁ : work₁ sourceIdx =
      (work₀ sourceIdx).move Dir3.left := by
    simpa [work₁] using
      captureSlotBitWork_source_internal sourceIdx highIdx true work₀
        hsourceHigh
  have hhigh₁ : (work₁ highIdx).HasBinaryNat
      (if slotBitAtHead (work₀ sourceIdx) then 1 else 0) := by
    simpa [work₁] using
      captureSlotBitWork_target_internal sourceIdx highIdx hsh true work₀
        hhighZero
  have hlow₁ : work₁ lowIdx = work₀ lowIdx := by
    simpa [work₁] using
      captureSlotBitWork_other_internal sourceIdx highIdx true work₀ lowIdx
        hsl.symm hlh (hwork lowIdx)
  have hsource₁read : (work₁ sourceIdx).read ≠ Γ.start := by
    rw [hsource₁]
    exact hsourceLow
  have hwork₁ : ∀ i, (work₁ i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      exact hsource₁read
    by_cases hih : i = highIdx
    · subst i
      exact hhigh₁.2.hasBinarySuffix.read_ne_start
    · rw [show work₁ i = work₀ i by
          simpa [work₁] using
            captureSlotBitWork_other_internal sourceIdx highIdx true work₀ i
              his hih (hwork i)]
      exact hwork i
  have hhigh := captureSlotBitTM_hoareTime_frame_internal sourceIdx highIdx
    hsh true inp₀ work₀ out₀ hinput hsourceHigh hwork houtput
  have hlow := captureSlotBitTM_hoareTime_frame_internal sourceIdx lowIdx
    hsl false inp₀ work₁ out₀ hinput hsource₁read hwork₁ houtput
  have htransition : ∀ inp work out,
      (inp = inp₀ ∧ work = work₁ ∧ out = out₀) →
      transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₁ ∧
        transitionTape out = out₀ := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact phaseTransition_eq_self_of_reads_ne_start hinput hwork₁ houtput
  simpa [captureSlotBitsTM, captureSlotBitsWork, work₁] using
    seqTM_hoareTime (captureSlotBitTM sourceIdx highIdx true)
      (captureSlotBitTM sourceIdx lowIdx false) hhigh htransition hlow

theorem captureSlotBitsTM_hoareTime_internal
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
      3 := by
  let work₁ := captureSlotBitWork sourceIdx highIdx true work₀
  have hsource₁ : work₁ sourceIdx =
      (work₀ sourceIdx).move Dir3.left := by
    simpa [work₁] using
      captureSlotBitWork_source_internal sourceIdx highIdx true work₀
        hsourceHigh
  have hsource₁read : (work₁ sourceIdx).read ≠ Γ.start := by
    rw [hsource₁]
    exact hsourceLow
  have hlow₁ : work₁ lowIdx = work₀ lowIdx := by
    simpa [work₁] using
      captureSlotBitWork_other_internal sourceIdx highIdx true work₀ lowIdx
        hsl.symm hlh (hwork lowIdx)
  have hframe := captureSlotBitsTM_hoareTime_frame_internal sourceIdx lowIdx
    highIdx hsl hsh hlh inp₀ work₀ out₀ hinput hsourceHigh hsourceLow hwork
    hhighZero houtput
  refine hframe.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    le_rfl
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩
  · simp [captureSlotBitsWork,
      captureSlotBitWork_source_internal sourceIdx lowIdx false work₁
        hsource₁read, hsource₁, work₁]
  · have hlow₁zero : (work₁ lowIdx).HasBinaryNat 0 := by
      simpa [hlow₁] using hlowZero
    have hlow := captureSlotBitWork_target_internal sourceIdx lowIdx hsl
      false work₁ hlow₁zero
    simpa [captureSlotBitsWork, work₁, hsource₁] using hlow
  · have hhigh₁ : (work₁ highIdx).HasBinaryNat
        (if slotBitAtHead (work₀ sourceIdx) then 1 else 0) := by
      simpa [work₁] using
        captureSlotBitWork_target_internal sourceIdx highIdx hsh true work₀
          hhighZero
    rw [captureSlotBitsWork,
      captureSlotBitWork_other_internal sourceIdx lowIdx false work₁ highIdx
        hsh.symm hlh.symm hhigh₁.2.hasBinarySuffix.read_ne_start]
    exact hhigh₁
  · intro i his hil hih
    rw [captureSlotBitsWork,
      captureSlotBitWork_other_internal sourceIdx lowIdx false work₁ i his hil]
    · exact captureSlotBitWork_other_internal sourceIdx highIdx true work₀ i
        his hih (hwork i)
    · by_cases hi : i = highIdx
      · exact absurd hi hih
      · rw [show work₁ i = work₀ i by
            simpa [work₁] using
              captureSlotBitWork_other_internal sourceIdx highIdx true work₀ i
                his hi (hwork i)]
        exact hwork i

theorem captureSlotBitsTM_hoareTimeSpace_internal
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
      3 inputLength (initialSpace + 3) := by
  apply (captureSlotBitsTM_hoareTime_internal sourceIdx lowIdx highIdx hsl hsh
    hlh inp₀ work₀ out₀ hinput hsourceHigh hsourceLow hwork hlowZero
    hhighZero houtput).toHoareTimeSpace
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  subst inp
  subst work
  subst out
  exact hinitial

theorem captureSlotBitTM_isTransducer_internal
    (sourceIdx targetIdx : Fin n) (moveLeft : Bool) :
    (captureSlotBitTM sourceIdx targetIdx moveLeft).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | capture =>
      cases hsource : wHeads sourceIdx <;>
        cases oHead <;>
        simp [captureSlotBitTM, hsource, TM.allIdle, TM.idleDir]
  | done =>
      cases oHead <;> simp [captureSlotBitTM, TM.allIdle, TM.idleDir]

theorem captureSlotBitsTM_isTransducer_internal
    (sourceIdx lowIdx highIdx : Fin n) :
    (captureSlotBitsTM sourceIdx lowIdx highIdx).IsTransducer := by
  exact (captureSlotBitTM_isTransducer_internal sourceIdx highIdx true).seqTM
    (captureSlotBitTM_isTransducer_internal sourceIdx lowIdx false)

end Machine

end BPCode

end Complexity
