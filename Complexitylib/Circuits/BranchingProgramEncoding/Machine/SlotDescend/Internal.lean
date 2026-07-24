/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotDescend.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotBranch
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotCapture

/-!
# Barrington recursive slot descent -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

private theorem prepareNextSlotDigitTM_step
    (sourceIdx lowIdx highIdx : Fin n)
    (hsl : sourceIdx ≠ lowIdx) (hsh : sourceIdx ≠ highIdx)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsource : (work₀ sourceIdx).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (prepareNextSlotDigitTM sourceIdx lowIdx highIdx).step
      { state := (prepareNextSlotDigitTM sourceIdx lowIdx highIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } =
      some
        { state := (prepareNextSlotDigitTM sourceIdx lowIdx highIdx).qhalt
          input := inp₀
          work := prepareNextSlotDigitWork sourceIdx lowIdx highIdx work₀
          output := out₀ } := by
  rw [TM.step, if_neg (by simp [prepareNextSlotDigitTM])]
  simp only [prepareNextSlotDigitTM]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · dsimp only
    simp [TM.idleDir, hinput, Tape.move]
  · dsimp only
    funext i
    by_cases his : i = sourceIdx
    · subst i
      simp [prepareNextSlotDigitWork, hsl, hsh, hsource]
    · by_cases hil : i = lowIdx
      · subst i
        simp [prepareNextSlotDigitWork, his, TM.idleDir, hwork lowIdx]
      · by_cases hih : i = highIdx
        · subst i
          simp [prepareNextSlotDigitWork, his, TM.idleDir,
            hwork highIdx]
        · simp [prepareNextSlotDigitWork, his, hil, hih, TM.idleDir,
            hwork i, Tape.move]
  · dsimp only
    simpa [TM.idleDir, houtput, Tape.move] using
      TM.writeAndMove_readBack out₀ houtput Dir3.stay

private theorem prepareNextSlotDigitWork_source
    (sourceIdx lowIdx highIdx : Fin n) (work : Fin n → Tape)
    (hsource : (work sourceIdx).read ≠ Γ.start) :
    prepareNextSlotDigitWork sourceIdx lowIdx highIdx work sourceIdx =
      (work sourceIdx).move Dir3.left := by
  simp only [prepareNextSlotDigitWork, if_pos]
  exact TM.writeAndMove_readBack (work sourceIdx) hsource Dir3.left

private theorem prepareNextSlotDigitWork_bit
    (sourceIdx lowIdx highIdx idx : Fin n)
    (his : idx ≠ sourceIdx) (hbit : idx = lowIdx ∨ idx = highIdx)
    (bit : Bool) (work : Fin n → Tape)
    (hvalue : (work idx).HasBinaryNat (if bit then 1 else 0)) :
    (prepareNextSlotDigitWork sourceIdx lowIdx highIdx work idx)
        |>.HasBinaryNat 0 := by
  simp only [prepareNextSlotDigitWork, if_neg his, if_pos hbit]
  rw [hvalue.eq_init_move_right]
  cases bit with
  | false =>
      change
        (((Tape.init []).move Dir3.right).writeAndMove .blank Dir3.stay)
          |>.HasBinaryNat 0
      rw [show
        (((Tape.init []).move Dir3.right).writeAndMove .blank Dir3.stay) =
          (Tape.init []).move Dir3.right by
            apply Tape.ext
            · rfl
            · funext i
              cases i with
              | zero =>
                  simp [Tape.writeAndMove, Tape.write, Tape.move, Tape.init]
              | succ i =>
                  cases i with
                  | zero =>
                      simp [Tape.writeAndMove, Tape.write, Tape.move, Tape.init]
                  | succ i =>
                      simp [Tape.writeAndMove, Tape.write, Tape.move,
                        Tape.init]]
      exact Tape.init_move_right_hasBinaryNat 0
  | true =>
      change
        (((Tape.init [Γ.one]).move Dir3.right).writeAndMove .blank Dir3.stay)
          |>.HasBinaryNat 0
      rw [show
        (((Tape.init [Γ.one]).move Dir3.right).writeAndMove .blank Dir3.stay) =
          (Tape.init []).move Dir3.right by
            apply Tape.ext
            · rfl
            · funext i
              cases i with
              | zero =>
                  simp [Tape.writeAndMove, Tape.write, Tape.move, Tape.init]
              | succ i =>
                  cases i with
                  | zero =>
                      simp [Tape.writeAndMove, Tape.write, Tape.move, Tape.init]
                  | succ i =>
                      simp [Tape.writeAndMove, Tape.write, Tape.move,
                        Tape.init]]
      exact Tape.init_move_right_hasBinaryNat 0

private theorem prepareNextSlotDigitWork_other
    (sourceIdx lowIdx highIdx : Fin n) (work : Fin n → Tape) (i : Fin n)
    (his : i ≠ sourceIdx) (hil : i ≠ lowIdx) (hih : i ≠ highIdx)
    (hread : (work i).read ≠ Γ.start) :
    prepareNextSlotDigitWork sourceIdx lowIdx highIdx work i = work i := by
  simpa [prepareNextSlotDigitWork, his, hil, hih, TM.idleDir, hread,
    Tape.move] using
      TM.writeAndMove_readBack (work i) hread Dir3.stay

theorem prepareNextSlotDigitTM_hoareTime_internal
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
      1 := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  subst inp
  subst work
  subst out
  have hstep := prepareNextSlotDigitTM_step sourceIdx lowIdx highIdx hsl hsh
    inp₀ work₀ out₀ hinput hsource hwork houtput
  refine ⟨_, 1, le_rfl, .step hstep .zero, rfl, ?_⟩
  refine ⟨rfl,
    prepareNextSlotDigitWork_source sourceIdx lowIdx highIdx work₀ hsource,
    prepareNextSlotDigitWork_bit sourceIdx lowIdx highIdx lowIdx hsl.symm
      (Or.inl rfl) low work₀ hlow,
    prepareNextSlotDigitWork_bit sourceIdx lowIdx highIdx highIdx hsh.symm
      (Or.inr rfl) high work₀ hhigh, ?_, rfl⟩
  intro i his hil hih
  exact prepareNextSlotDigitWork_other sourceIdx lowIdx highIdx work₀ i his hil
    hih (hwork i)

theorem recaptureSlotBitsTM_hoareTime_internal
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
      recaptureSlotBitsTime := by
  have hrole : ∀ i j : Fin 5, i ≠ j → layout.roles i ≠ layout.roles j :=
    fun _ _ hij => layout.roles.injective.ne hij
  have hsl : layout.sourceIdx ≠ layout.lowIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.lowIdx
    exact hrole 0 3 (by decide)
  have hsh : layout.sourceIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.sourceIdx BarringtonSlotLayout.highIdx
    exact hrole 0 4 (by decide)
  have hlh : layout.lowIdx ≠ layout.highIdx := by
    unfold BarringtonSlotLayout.lowIdx BarringtonSlotLayout.highIdx
    exact hrole 3 4 (by decide)
  let prepared : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    work layout.sourceIdx = (work₀ layout.sourceIdx).move Dir3.left ∧
    (work layout.lowIdx).HasBinaryNat 0 ∧
    (work layout.highIdx).HasBinaryNat 0 ∧
    (∀ i, i ≠ layout.sourceIdx → i ≠ layout.lowIdx →
      i ≠ layout.highIdx → work i = work₀ i) ∧
    out = out₀
  have hprepare := prepareNextSlotDigitTM_hoareTime_internal layout.sourceIdx
    layout.lowIdx layout.highIdx hsl hsh previousLow previousHigh inp₀ work₀
    out₀ hinput (hwork layout.sourceIdx) hwork hlow hhigh houtput
  have hpreparedReads : ∀ inp work out, prepared inp work out →
      ∀ i, (work i).read ≠ Γ.start := by
    intro inp work out hpre i
    rcases hpre with ⟨-, hsource, hlowZero, hhighZero, hother, -⟩
    by_cases his : i = layout.sourceIdx
    · subst i
      rw [hsource, Tape.read, Tape.move, hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work₀ layout.sourceIdx).head - 1)
        (by rw [hsourceHead, hslot.2.1]; omega)
    by_cases hil : i = layout.lowIdx
    · subst i
      exact hlowZero.2.hasBinarySuffix.read_ne_start
    by_cases hih : i = layout.highIdx
    · subst i
      exact hhighZero.2.hasBinarySuffix.read_ne_start
    · rw [hother i his hil hih]
      exact hwork i
  have hcapture :
      (captureSlotBitsTM layout.sourceIdx layout.lowIdx layout.highIdx)
        |>.HoareTime prepared
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
          3 := by
    intro inp work out hpre
    rcases hpre with ⟨hinp, hsource, hlowZero, hhighZero, hother, hout⟩
    have hsourceHigh : (work layout.sourceIdx).read ≠ Γ.start :=
      hpreparedReads inp work out
        ⟨hinp, hsource, hlowZero, hhighZero, hother, hout⟩ layout.sourceIdx
    have hsourceLow : ((work layout.sourceIdx).move Dir3.left).read ≠
        Γ.start := by
      rw [Tape.read, Tape.move, hsource, Tape.move, hsourceCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        (((work₀ layout.sourceIdx).head - 1) - 1)
        (by rw [hsourceHead, hslot.2.1]; omega)
    have hrun := captureSlotBitsTM_hoareTime layout.sourceIdx layout.lowIdx
      layout.highIdx hsl hsh hlh inp work out
      (by rw [hinp]; exact hinput) hsourceHigh hsourceLow
      (hpreparedReads inp work out
        ⟨hinp, hsource, hlowZero, hhighZero, hother, hout⟩)
      hlowZero hhighZero (by rw [hout]; exact houtput)
    obtain ⟨c, time, htime, hreach, hhalt, hpost⟩ :=
      hrun inp work out ⟨rfl, rfl, rfl⟩
    rcases hpost with
      ⟨hcInput, hcSource, hcLow, hcHigh, hcOther, hcOutput⟩
    refine ⟨c, time, htime, hreach, hhalt, ?_⟩
    refine ⟨hcInput.trans hinp,
      ?_, ?_, ?_, ?_, ?_, hcOutput.trans hout⟩
    · rw [hcSource, hsource, Tape.move, Tape.move, hsourceHead]
      have horiginalHead : original.head = 1 := hslot.2.1
      dsimp only
      omega
    · rw [hcSource, hsource, Tape.move, Tape.move, hsourceCells]
    · rw [← slotBitAtHead_eq_testBit_of_cells
          ((work layout.sourceIdx).move Dir3.left) original slotValue
            (2 * fuel) hslot]
      · exact hcLow
      · rw [hsource, Tape.move, Tape.move, hsourceCells]
      · rw [hsource, Tape.move, Tape.move, hsourceHead, hslot.2.1]
        have horiginalHead : original.head = 1 := hslot.2.1
        dsimp only
        omega
    · rw [← slotBitAtHead_eq_testBit_of_cells
          (work layout.sourceIdx) original slotValue (2 * fuel + 1) hslot]
      · exact hcHigh
      · rw [hsource, Tape.move, hsourceCells]
      · rw [hsource, Tape.move, hsourceHead, hslot.2.1]
        have horiginalHead : original.head = 1 := hslot.2.1
        dsimp only
        omega
    · intro i his hil hih
      rw [hcOther i his hil hih]
      exact hother i his hil hih
  have htransition : ∀ inp work out, prepared inp work out →
      prepared (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hpre
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      (inp := inp) (work := work) (out := out)
      (by rw [hpre.1]; exact hinput) (hpreparedReads inp work out hpre)
      (by rw [hpre.2.2.2.2.2]; exact houtput)
    rw [hi, hw, ho]
    exact hpre
  simpa [recaptureSlotBitsTM, recaptureSlotBitsTime, prepared] using
    TM.seqTM_hoareTime _ _ hprepare htransition hcapture

theorem recaptureSlotBitsTM_hoareTimeSpace_internal
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
      (recaptureSlotBitsSpace initialSpace) := by
  apply (recaptureSlotBitsTM_hoareTime_internal layout slotValue fuel
    previousLow previousHigh original inp₀ work₀ out₀ hinput hslot hsourceHead
    hsourceCells hlow hhigh hwork houtput).toHoareTimeSpace
  intro inp work out hpre
  rcases hpre with ⟨rfl, rfl, rfl⟩
  constructor
  · exact hworkSpace
  · exact hinputSpace

theorem barringtonNextSlotBranchTM_selected_hoareTimeSpace_internal
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
        (recaptureSlotBitsSpace initialSpace) := by
  let captured : TapePred n := fun inp work out =>
    inp = inp₀ ∧
    (work layout.sourceIdx).head = original.head + 2 * fuel ∧
    (work layout.sourceIdx).cells = original.cells ∧
    (work layout.lowIdx).HasBinaryNat
      (if slotValue.testBit (2 * fuel) then 1 else 0) ∧
    (work layout.highIdx).HasBinaryNat
      (if slotValue.testBit (2 * fuel + 1) then 1 else 0) ∧
    (∀ i, i ≠ layout.sourceIdx → i ≠ layout.lowIdx →
      i ≠ layout.highIdx → work i = work₀ i) ∧
    out = out₀
  have hcapture := recaptureSlotBitsTM_hoareTimeSpace_internal layout
    slotValue fuel previousLow previousHigh original inputLength initialSpace
    inp₀ work₀ out₀ hinput hslot hsourceHead hsourceCells hlow hhigh hwork
    houtput hworkSpace hinputSpace
  have hcapturedReads : ∀ inp work out, captured inp work out →
      ∀ i, (work i).read ≠ Γ.start := by
    intro inp work out hcap i
    rcases hcap with
      ⟨-, hcapturedHead, hcapturedCells, hcapturedLow, hcapturedHigh,
        hother, -⟩
    by_cases his : i = layout.sourceIdx
    · subst i
      rw [Tape.read, hcapturedCells]
      exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
        ((work layout.sourceIdx).head)
        (by rw [hcapturedHead, hslot.2.1]; omega)
    by_cases hil : i = layout.lowIdx
    · subst i
      exact hcapturedLow.2.hasBinarySuffix.read_ne_start
    by_cases hih : i = layout.highIdx
    · subst i
      exact hcapturedHigh.2.hasBinarySuffix.read_ne_start
    · rw [hother i his hil hih]
      exact hwork i
  have hbranch := barringtonSlotBranchTM_selected_hoareTimeSpace layout.lowIdx
    layout.highIdx reversed (slotValue.testBit (2 * fuel))
    (slotValue.testBit (2 * fuel + 1)) onLeft onRight onInverseLeft
    onInverseRight
    (fun inp work out hcap => by rw [hcap.1]; exact hinput)
    hcapturedReads
    (fun inp work out hcap => by rw [hcap.2.2.2.2.2.2]; exact houtput)
    (fun _ _ _ hcap => hcap.2.2.2.1)
    (fun _ _ _ hcap => hcap.2.2.2.2.1)
    hselected
  have htransition : ∀ inp work out, captured inp work out →
      captured (TM.transitionInput inp)
        (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
    intro inp work out hcap
    obtain ⟨hi, hw, ho⟩ := TM.phaseTransition_eq_self_of_reads_ne_start
      (inp := inp) (work := work) (out := out)
      (by rw [hcap.1]; exact hinput) (hcapturedReads inp work out hcap)
      (by rw [hcap.2.2.2.2.2.2]; exact houtput)
    rw [hi, hw, ho]
    exact hcap
  simpa [barringtonNextSlotBranchTM, barringtonNextSlotBranchTime, captured]
    using TM.seqTM_hoareTimeSpace _ _ hcapture htransition hbranch

theorem prepareNextSlotDigitTM_isTransducer_internal
    (sourceIdx lowIdx highIdx : Fin n) :
    (prepareNextSlotDigitTM sourceIdx lowIdx highIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | prepare =>
      cases oHead <;> simp [prepareNextSlotDigitTM, TM.idleDir]
  | done =>
      cases oHead <;> simp [prepareNextSlotDigitTM, TM.allIdle, TM.idleDir]

theorem recaptureSlotBitsTM_isTransducer_internal
    (layout : BarringtonSlotLayout n) :
    (recaptureSlotBitsTM layout).IsTransducer := by
  exact (prepareNextSlotDigitTM_isTransducer_internal layout.sourceIdx
    layout.lowIdx layout.highIdx).seqTM
      (captureSlotBitsTM_isTransducer layout.sourceIdx layout.lowIdx
        layout.highIdx)

theorem barringtonNextSlotBranchTM_isTransducer_internal
    (layout : BarringtonSlotLayout n) (reversed : Bool)
    {onLeft onRight onInverseLeft onInverseRight : TM n}
    (hleft : onLeft.IsTransducer) (hright : onRight.IsTransducer)
    (hinverseLeft : onInverseLeft.IsTransducer)
    (hinverseRight : onInverseRight.IsTransducer) :
    (barringtonNextSlotBranchTM layout reversed onLeft onRight onInverseLeft
      onInverseRight).IsTransducer := by
  exact (recaptureSlotBitsTM_isTransducer_internal layout).seqTM
    (barringtonSlotBranchTM_isTransducer layout.lowIdx layout.highIdx reversed
      hleft hright hinverseLeft hinverseRight)

end Machine

end BPCode

end Complexity
