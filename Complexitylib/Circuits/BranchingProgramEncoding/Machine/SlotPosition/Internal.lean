/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotPosition.Defs
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Barrington slot positioning -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

private theorem moveSlotRightWork_apply
    (sourceIdx : Fin n) (work : Fin n → Tape)
    (hwork : ∀ i, (work i).read ≠ Γ.start) (i : Fin n) :
    (fun j =>
      (work j).writeAndMove (TM.readBackWrite (work j).read)
        (if j = sourceIdx then Dir3.right else TM.idleDir (work j).read)) i =
      moveSlotRightWork sourceIdx work i := by
  by_cases his : i = sourceIdx
  · subst i
    simp only [moveSlotRightWork, Function.update_self, ↓reduceIte]
    exact TM.writeAndMove_readBack (work sourceIdx) (hwork sourceIdx)
      Dir3.right
  · simp only [moveSlotRightWork, Function.update_of_ne his, if_neg his]
    simpa [TM.idleDir, hwork i, Tape.move] using
      TM.writeAndMove_readBack (work i) (hwork i) Dir3.stay

private theorem moveSlotRightTM_step
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (moveSlotRightTM sourceIdx).step
      { state := (moveSlotRightTM sourceIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } =
      some
        { state := (moveSlotRightTM sourceIdx).qhalt
          input := inp₀
          work := moveSlotRightWork sourceIdx work₀
          output := out₀ } := by
  rw [TM.step, if_neg (by simp [moveSlotRightTM])]
  simp only [moveSlotRightTM]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · dsimp only
    exact TM.transitionInput_eq_self hinput
  · dsimp only
    funext i
    exact moveSlotRightWork_apply sourceIdx work₀ hwork i
  · dsimp only
    exact TM.transitionTape_eq_self houtput

theorem moveSlotRightTM_hoareTime_internal
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (moveSlotRightTM sourceIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = moveSlotRightWork sourceIdx work₀ ∧ out = out₀)
      1 := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  rw [hinp, hworkEq, hout]
  have hstep := moveSlotRightTM_step sourceIdx inp₀ work₀ out₀ hinput hwork
    houtput
  exact ⟨_, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

private theorem advanceSlotDigitTM_step
    (sourceIdx : Fin n) (phase next : AdvanceSlotDigitPhase)
    (hphase : phase = .first ∧ next = .second ∨
      phase = .second ∧ next = .done)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (advanceSlotDigitTM sourceIdx).step
      { state := phase, input := inp₀, work := work₀, output := out₀ } =
      some
        { state := next
          input := inp₀
          work := moveSlotRightWork sourceIdx work₀
          output := out₀ } := by
  rcases hphase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [TM.step, if_neg (by simp [advanceSlotDigitTM])] <;>
    simp only [advanceSlotDigitTM] <;>
    refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  all_goals dsimp only
  · exact TM.transitionInput_eq_self hinput
  · funext i
    exact moveSlotRightWork_apply sourceIdx work₀ hwork i
  · exact TM.transitionTape_eq_self houtput
  · exact TM.transitionInput_eq_self hinput
  · funext i
    exact moveSlotRightWork_apply sourceIdx work₀ hwork i
  · exact TM.transitionTape_eq_self houtput

theorem advanceSlotDigitTM_reachesIn_frame_internal
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceNext : ((work₀ sourceIdx).move Dir3.right).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (advanceSlotDigitTM sourceIdx).reachesIn 2
      { state := (advanceSlotDigitTM sourceIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (advanceSlotDigitTM sourceIdx).qhalt
        input := inp₀
        work := moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx work₀)
        output := out₀ } := by
  let work₁ := moveSlotRightWork sourceIdx work₀
  have hwork₁source : work₁ sourceIdx =
      (work₀ sourceIdx).move Dir3.right := by
    simp [work₁, moveSlotRightWork]
  have hwork₁ : ∀ i, (work₁ i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      rw [hwork₁source]
      exact hsourceNext
    · simp [work₁, moveSlotRightWork, his]
      exact hwork i
  have hfirst := advanceSlotDigitTM_step sourceIdx .first .second
    (Or.inl ⟨rfl, rfl⟩) inp₀ work₀ out₀ hinput hwork houtput
  have hsecond := advanceSlotDigitTM_step sourceIdx .second .done
    (Or.inr ⟨rfl, rfl⟩) inp₀ work₁ out₀ hinput hwork₁ houtput
  exact .step hfirst (.step (by simpa [work₁] using hsecond) .zero)

theorem advanceSlotDigitTM_hoareTime_internal
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
      2 := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  rw [hinp, hworkEq, hout]
  let final : Cfg n (advanceSlotDigitTM sourceIdx).Q :=
    { state := .done
      input := inp₀
      work := moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx work₀)
      output := out₀ }
  refine ⟨final, 2, le_rfl, ?_, ?_, ?_⟩
  · exact advanceSlotDigitTM_reachesIn_frame_internal sourceIdx inp₀ work₀
      out₀ hinput hsourceNext hwork houtput
  · rfl
  · exact ⟨rfl, rfl, rfl⟩

private def positionSlotTapeAt (tape : Tape) (value : ℕ) : Tape :=
  { tape with head := tape.head + 2 * value }

private def positionSlotWorkAt (work : Fin n → Tape)
    (sourceIdx counterIdx : Fin n) (value : ℕ) : Fin n → Tape :=
  Function.update
    (Function.update work sourceIdx (positionSlotTapeAt (work sourceIdx) value))
    counterIdx ((Tape.init (value.bits.map Γ.ofBool)).move Dir3.right)

private theorem positionSlotWorkAt_source
    (work : Fin n → Tape) (sourceIdx counterIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (value : ℕ) :
    positionSlotWorkAt work sourceIdx counterIdx value sourceIdx =
      positionSlotTapeAt (work sourceIdx) value := by
  simp [positionSlotWorkAt, hsc]

private theorem positionSlotWorkAt_counter
    (work : Fin n → Tape) (sourceIdx counterIdx : Fin n) (value : ℕ) :
    (positionSlotWorkAt work sourceIdx counterIdx value counterIdx)
        |>.HasBinaryNat value := by
  simp only [positionSlotWorkAt, Function.update_self]
  exact Tape.init_move_right_hasBinaryNat value

private theorem positionSlotWorkAt_other
    (work : Fin n → Tape) (sourceIdx counterIdx i : Fin n)
    (his : i ≠ sourceIdx) (hic : i ≠ counterIdx) (value : ℕ) :
    positionSlotWorkAt work sourceIdx counterIdx value i = work i := by
  simp [positionSlotWorkAt, his, hic]

private theorem positionSlotWorkAt_zero_eq
    (work : Fin n → Tape) (sourceIdx counterIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx)
    (hcounter : (work counterIdx).HasBinaryNat 0) :
    positionSlotWorkAt work sourceIdx counterIdx 0 = work := by
  funext i
  by_cases hic : i = counterIdx
  · subst i
    simp only [positionSlotWorkAt, Function.update_self]
    exact (Tape.HasBinaryNat.eq_init_move_right hcounter).symm
  by_cases his : i = sourceIdx
  · subst i
    simp [positionSlotWorkAt, hsc, positionSlotTapeAt]
  · exact positionSlotWorkAt_other work sourceIdx counterIdx i his hic 0

private theorem positionSlotTapeAt_read_ne_start
    {tape : Tape} {slotValue value : ℕ}
    (hslot : tape.HasBinaryNat slotValue) :
    (positionSlotTapeAt tape value).read ≠ Γ.start := by
  rw [Tape.read]
  exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
    (tape.head + 2 * value) (by rw [hslot.2.1]; omega)

private theorem positionSlotTapeAt_move_read_ne_start
    {tape : Tape} {slotValue value : ℕ}
    (hslot : tape.HasBinaryNat slotValue) :
    ((positionSlotTapeAt tape value).move Dir3.right).read ≠ Γ.start := by
  rw [Tape.read]
  exact Tape.HasBinaryContent.cells_ne_start hslot.2.2
    (tape.head + 2 * value + 1) (by rw [hslot.2.1]; omega)

private theorem positionSlotWorkAt_read_ne_start
    (work : Fin n → Tape) (sourceIdx counterIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (slotValue value : ℕ)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hwork : ∀ i, (work i).read ≠ Γ.start) :
    ∀ i, (positionSlotWorkAt work sourceIdx counterIdx value i).read ≠
      Γ.start := by
  intro i
  by_cases hic : i = counterIdx
  · subst i
    exact (positionSlotWorkAt_counter work sourceIdx counterIdx value).2
      |>.hasBinarySuffix.read_ne_start
  by_cases his : i = sourceIdx
  · subst i
    rw [positionSlotWorkAt_source work sourceIdx counterIdx hsc]
    exact positionSlotTapeAt_read_ne_start hslot
  · rw [positionSlotWorkAt_other work sourceIdx counterIdx i his hic]
    exact hwork i

private theorem moveSlotRightWork_twice_source
    (work : Fin n → Tape) (sourceIdx counterIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (value : ℕ) :
    moveSlotRightWork sourceIdx
        (moveSlotRightWork sourceIdx
          (positionSlotWorkAt work sourceIdx counterIdx value)) sourceIdx =
      positionSlotTapeAt (work sourceIdx) (value + 1) := by
  rw [moveSlotRightWork, Function.update_self, moveSlotRightWork,
    Function.update_self,
    positionSlotWorkAt_source work sourceIdx counterIdx hsc]
  cases work sourceIdx
  simp [positionSlotTapeAt, Tape.move]
  omega

private theorem moveSlotRightWork_twice_counter
    (work : Fin n → Tape) (sourceIdx counterIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (value : ℕ) :
    moveSlotRightWork sourceIdx
        (moveSlotRightWork sourceIdx
          (positionSlotWorkAt work sourceIdx counterIdx value)) counterIdx =
      positionSlotWorkAt work sourceIdx counterIdx value counterIdx := by
  simp [moveSlotRightWork, hsc.symm]

private theorem moveSlotRightWork_twice_other
    (work : Fin n → Tape) (sourceIdx counterIdx i : Fin n)
    (his : i ≠ sourceIdx) (hic : i ≠ counterIdx) (value : ℕ) :
    moveSlotRightWork sourceIdx
        (moveSlotRightWork sourceIdx
          (positionSlotWorkAt work sourceIdx counterIdx value)) i = work i := by
  simp [moveSlotRightWork, his,
    positionSlotWorkAt_other work sourceIdx counterIdx i his hic]

private def positionSlotScanCfg
    (sourceIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (positionSlotLoopTM sourceIdx counterIdx limitIdx).Q :=
  { state := .inl (.scan true)
    input := inp
    work := positionSlotWorkAt work sourceIdx counterIdx value
    output := out }

private def positionSlotIterationStartCfg
    (sourceIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (positionSlotLoopTM sourceIdx counterIdx limitIdx).Q :=
  { state := .inr
      (TM.binaryForIterationTM (advanceSlotDigitTM sourceIdx) counterIdx).qstart
    input := inp
    work := positionSlotWorkAt work sourceIdx counterIdx value
    output := out }

private def positionSlotIterationDoneCfg
    (sourceIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (value : ℕ) :
    Cfg n (positionSlotLoopTM sourceIdx counterIdx limitIdx).Q :=
  { state := .inr
      (TM.binaryForIterationTM (advanceSlotDigitTM sourceIdx) counterIdx).qhalt
    input := inp
    work := positionSlotWorkAt work sourceIdx counterIdx (value + 1)
    output := out }

private def positionSlotDoneCfg
    (sourceIdx counterIdx limitIdx : Fin n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) (fuel : ℕ) :
    Cfg n (positionSlotLoopTM sourceIdx counterIdx limitIdx).Q :=
  { state := .inl .done
    input := inp
    work := positionSlotWorkAt work sourceIdx counterIdx fuel
    output := out }

private theorem positionSlotAdvance_reachesIn
    (sourceIdx counterIdx : Fin n) (hsc : sourceIdx ≠ counterIdx)
    (slotValue value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinput : inp.read ≠ Γ.start)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (advanceSlotDigitTM sourceIdx).reachesIn 2
      { state := (advanceSlotDigitTM sourceIdx).qstart
        input := inp
        work := positionSlotWorkAt work sourceIdx counterIdx value
        output := out }
      { state := (advanceSlotDigitTM sourceIdx).qhalt
        input := inp
        work := moveSlotRightWork sourceIdx
          (moveSlotRightWork sourceIdx
            (positionSlotWorkAt work sourceIdx counterIdx value))
        output := out } := by
  apply advanceSlotDigitTM_reachesIn_frame_internal sourceIdx inp
  · exact hinput
  · rw [positionSlotWorkAt_source work sourceIdx counterIdx hsc]
    exact positionSlotTapeAt_move_read_ne_start hslot
  · exact positionSlotWorkAt_read_ne_start work sourceIdx counterIdx hsc
      slotValue value hslot hwork
  · exact houtput

private theorem positionSlotSucc_reachesIn
    (sourceIdx counterIdx : Fin n) (hsc : sourceIdx ≠ counterIdx)
    (slotValue value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinput : inp.read ≠ Γ.start)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (TM.binarySuccTM counterIdx).reachesIn (TM.binarySuccTime value)
      { state := (TM.binarySuccTM counterIdx).qstart
        input := inp
        work := moveSlotRightWork sourceIdx
          (moveSlotRightWork sourceIdx
            (positionSlotWorkAt work sourceIdx counterIdx value))
        output := out }
      { state := (TM.binarySuccTM counterIdx).qhalt
        input := inp
        work := positionSlotWorkAt work sourceIdx counterIdx (value + 1)
        output := out } := by
  let advanced := moveSlotRightWork sourceIdx
    (moveSlotRightWork sourceIdx
      (positionSlotWorkAt work sourceIdx counterIdx value))
  have hcounter : (advanced counterIdx).HasBinaryNat value := by
    rw [show advanced counterIdx =
        positionSlotWorkAt work sourceIdx counterIdx value counterIdx by
      exact moveSlotRightWork_twice_counter work sourceIdx counterIdx hsc value]
    exact positionSlotWorkAt_counter work sourceIdx counterIdx value
  have hadvancedRead : ∀ i, (advanced i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      rw [show advanced sourceIdx =
          positionSlotTapeAt (work sourceIdx) (value + 1) by
        exact moveSlotRightWork_twice_source work sourceIdx counterIdx hsc value]
      exact positionSlotTapeAt_read_ne_start hslot
    by_cases hic : i = counterIdx
    · subst i
      exact hcounter.2.hasBinarySuffix.read_ne_start
    · rw [show advanced i = work i by
          exact moveSlotRightWork_twice_other work sourceIdx counterIdx i his
            hic value]
      exact hwork i
  obtain ⟨c', hreach, hhalt, hinp, hother, hcounter', hout⟩ :=
    TM.binarySuccTM_reachesIn_frame counterIdx value inp advanced out hcounter
      hinput (fun i _ => hadvancedRead i) houtput
  have hworkEq : c'.work =
      positionSlotWorkAt work sourceIdx counterIdx (value + 1) := by
    funext i
    by_cases hic : i = counterIdx
    · subst i
      simp only [positionSlotWorkAt, Function.update_self]
      exact Tape.HasBinaryNat.eq_init_move_right hcounter'
    by_cases his : i = sourceIdx
    · subst i
      rw [hother sourceIdx hsc,
        positionSlotWorkAt_source work sourceIdx counterIdx hsc]
      exact moveSlotRightWork_twice_source work sourceIdx counterIdx hsc value
    · rw [hother i hic,
        positionSlotWorkAt_other work sourceIdx counterIdx i his hic]
      exact moveSlotRightWork_twice_other work sourceIdx counterIdx i his hic
        value
  have hc' : c' =
      { state := (TM.binarySuccTM counterIdx).qhalt
        input := inp
        work := positionSlotWorkAt work sourceIdx counterIdx (value + 1)
        output := out } :=
    Cfg.ext hhalt hinp hworkEq hout
  simpa [advanced, hc'] using hreach

private theorem positionSlotIteration_reachesIn
    (sourceIdx counterIdx limitIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (slotValue value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinput : inp.read ≠ Γ.start)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn
      (TM.binaryForIterationTime (fun _ => 2) value)
      (positionSlotIterationStartCfg sourceIdx counterIdx limitIdx inp work out
        value)
      (positionSlotIterationDoneCfg sourceIdx counterIdx limitIdx inp work out
        value) := by
  let body := advanceSlotDigitTM sourceIdx
  let succ := TM.binarySuccTM counterIdx
  let current := positionSlotWorkAt work sourceIdx counterIdx value
  let advanced := moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx current)
  have hbody := positionSlotAdvance_reachesIn sourceIdx counterIdx hsc
    slotValue value inp work out hinput hslot hwork houtput
  have hsucc := positionSlotSucc_reachesIn sourceIdx counterIdx hsc
    slotValue value inp work out hinput hslot hwork houtput
  have hadvancedRead : ∀ i, (advanced i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      rw [show advanced sourceIdx =
          positionSlotTapeAt (work sourceIdx) (value + 1) by
        exact moveSlotRightWork_twice_source work sourceIdx counterIdx hsc value]
      exact positionSlotTapeAt_read_ne_start hslot
    by_cases hic : i = counterIdx
    · subst i
      rw [show advanced counterIdx = current counterIdx by
        exact moveSlotRightWork_twice_counter work sourceIdx counterIdx hsc value]
      exact (positionSlotWorkAt_counter work sourceIdx counterIdx value).2
        |>.hasBinarySuffix.read_ne_start
    · rw [show advanced i = work i by
          exact moveSlotRightWork_twice_other work sourceIdx counterIdx i his
            hic value]
      exact hwork i
  obtain ⟨hinpTransition, hworkTransition, houtTransition⟩ :=
    TM.phaseTransition_eq_self_of_reads_ne_start hinput hadvancedRead houtput
  have hsucc' : succ.reachesIn (TM.binarySuccTime value)
      { state := succ.qstart
        input := TM.transitionInput inp
        work := fun i => TM.transitionTape (advanced i)
        output := TM.transitionTape out }
      { state := succ.qhalt
        input := inp
        work := positionSlotWorkAt work sourceIdx counterIdx (value + 1)
        output := out } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hsucc
  have hseq := TM.seqTM_reachesIn_of_reachesIn body succ hbody rfl hsucc'
  have hlift := TM.binaryForTM_iteration_reachesIn_internal body counterIdx
    limitIdx hseq
  simpa [body, succ, current, advanced, positionSlotLoopTM,
    positionSlotIterationStartCfg, positionSlotIterationDoneCfg,
    TM.binaryForIterationTime, TM.binaryForIterationTM,
    TM.binaryForIterationWrap, TM.phase1Wrap, TM.phase2Wrap] using hlift

private theorem positionSlotLoopback_step
    (sourceIdx counterIdx limitIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (slotValue value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinput : inp.read ≠ Γ.start)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).step
      (positionSlotIterationDoneCfg sourceIdx counterIdx limitIdx inp work out
        value) =
      some (positionSlotScanCfg sourceIdx counterIdx limitIdx inp work out
        (value + 1)) := by
  let iteration :=
    TM.binaryForIterationTM (advanceSlotDigitTM sourceIdx) counterIdx
  let c : Cfg n iteration.Q :=
    { state := iteration.qhalt
      input := inp
      work := positionSlotWorkAt work sourceIdx counterIdx (value + 1)
      output := out }
  have hworkAt := positionSlotWorkAt_read_ne_start work sourceIdx counterIdx hsc
    slotValue (value + 1) hslot hwork
  have hstep := TM.binaryForTM_step_iteration_halt_internal
    (advanceSlotDigitTM sourceIdx) counterIdx limitIdx c rfl hinput hworkAt
    houtput
  simpa [c, iteration, positionSlotLoopTM, positionSlotIterationDoneCfg,
    positionSlotScanCfg, TM.binaryForIterationWrap] using hstep

private theorem positionSlotTest_reachesIn
    (sourceIdx counterIdx limitIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (hcl : counterIdx ≠ limitIdx)
    (hsl : sourceIdx ≠ limitIdx)
    (slotValue fuel value : ℕ) (hlt : value < fuel)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinput : inp.read ≠ Γ.start)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hlimit : (work limitIdx).HasBinaryNat fuel)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn
      (TM.binaryForCompareTime fuel)
      (positionSlotScanCfg sourceIdx counterIdx limitIdx inp work out value)
      (positionSlotIterationStartCfg sourceIdx counterIdx limitIdx inp work out
        value) := by
  have hlimitAt :
      (positionSlotWorkAt work sourceIdx counterIdx value limitIdx)
        |>.HasBinaryNat fuel := by
    rw [positionSlotWorkAt_other work sourceIdx counterIdx limitIdx hsl.symm
      hcl.symm]
    exact hlimit
  have hrun := TM.binaryForTM_compare_reachesIn_frame_of_lt
    (advanceSlotDigitTM sourceIdx) counterIdx limitIdx hcl value fuel hlt inp
    (positionSlotWorkAt work sourceIdx counterIdx value) out
    (positionSlotWorkAt_counter work sourceIdx counterIdx value) hlimitAt
    hinput
    (fun i _ _ => positionSlotWorkAt_read_ne_start work sourceIdx counterIdx
      hsc slotValue value hslot hwork i)
    houtput
  simpa [positionSlotLoopTM, positionSlotScanCfg,
    positionSlotIterationStartCfg] using hrun

private theorem positionSlotDone_reachesIn
    (sourceIdx counterIdx limitIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (hcl : counterIdx ≠ limitIdx)
    (hsl : sourceIdx ≠ limitIdx)
    (slotValue fuel : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinput : inp.read ≠ Γ.start)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hlimit : (work limitIdx).HasBinaryNat fuel)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn
      (TM.binaryForCompareTime fuel)
      (positionSlotScanCfg sourceIdx counterIdx limitIdx inp work out fuel)
      (positionSlotDoneCfg sourceIdx counterIdx limitIdx inp work out fuel) := by
  have hlimitAt :
      (positionSlotWorkAt work sourceIdx counterIdx fuel limitIdx)
        |>.HasBinaryNat fuel := by
    rw [positionSlotWorkAt_other work sourceIdx counterIdx limitIdx hsl.symm
      hcl.symm]
    exact hlimit
  have hrun := TM.binaryForTM_compare_reachesIn_frame_of_eq
    (advanceSlotDigitTM sourceIdx) counterIdx limitIdx hcl fuel inp
    (positionSlotWorkAt work sourceIdx counterIdx fuel) out
    (positionSlotWorkAt_counter work sourceIdx counterIdx fuel) hlimitAt hinput
    (fun i _ _ => positionSlotWorkAt_read_ne_start work sourceIdx counterIdx
      hsc slotValue fuel hslot hwork i)
    houtput
  simpa [positionSlotLoopTM, positionSlotScanCfg, positionSlotDoneCfg] using hrun

private def positionSlotLoopSpec
    (sourceIdx counterIdx limitIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx) (hcl : counterIdx ≠ limitIdx)
    (hsl : sourceIdx ≠ limitIdx)
    (slotValue fuel : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hinput : inp.read ≠ Γ.start)
    (hslot : (work sourceIdx).HasBinaryNat slotValue)
    (hlimit : (work limitIdx).HasBinaryNat fuel)
    (hwork : ∀ i, (work i).read ≠ Γ.start)
    (houtput : out.read ≠ Γ.start) :
    TM.BinaryForLoopSpec (advanceSlotDigitTM sourceIdx) counterIdx limitIdx
      (fun _ => 2) fuel where
  counter_ne_limit := hcl
  scanCfg := positionSlotScanCfg sourceIdx counterIdx limitIdx inp work out
  iterationStartCfg :=
    positionSlotIterationStartCfg sourceIdx counterIdx limitIdx inp work out
  iterationDoneCfg :=
    positionSlotIterationDoneCfg sourceIdx counterIdx limitIdx inp work out
  doneCfg := positionSlotDoneCfg sourceIdx counterIdx limitIdx inp work out fuel
  testRun value hvalue := positionSlotTest_reachesIn sourceIdx counterIdx
    limitIdx hsc hcl hsl slotValue fuel value hvalue inp work out hinput hslot
    hlimit hwork houtput
  iterationRun value _ := positionSlotIteration_reachesIn sourceIdx counterIdx
    limitIdx hsc slotValue value inp work out hinput hslot hwork houtput
  loopbackStep value _ := positionSlotLoopback_step sourceIdx counterIdx
    limitIdx hsc slotValue value inp work out hinput hslot hwork houtput
  doneRun := positionSlotDone_reachesIn sourceIdx counterIdx limitIdx hsc hcl
    hsl slotValue fuel inp work out hinput hslot hlimit hwork houtput

theorem positionSlotLoopTM_reachesIn_frame_internal
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
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn
      (positionSlotLoopTime fuel)
      { state := (positionSlotLoopTM sourceIdx counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ }
      { state := (positionSlotLoopTM sourceIdx counterIdx limitIdx).qhalt
        input := inp₀
        work := positionSlotWorkAt work₀ sourceIdx counterIdx fuel
        output := out₀ } := by
  let spec := positionSlotLoopSpec sourceIdx counterIdx limitIdx hsc hcl hsl
    slotValue fuel inp₀ work₀ out₀ hinput hslot hlimit hwork houtput
  have hrun := spec.reachesIn fuel 0 (by omega)
  have hstart : spec.scanCfg 0 =
      { state := (positionSlotLoopTM sourceIdx counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, positionSlotLoopSpec, positionSlotScanCfg]
    rw [positionSlotWorkAt_zero_eq work₀ sourceIdx counterIdx hsc hcounter]
    rfl
  rw [hstart] at hrun
  simpa [spec, positionSlotLoopSpec, positionSlotDoneCfg,
    positionSlotLoopTime, positionSlotLoopTM, TM.binaryForTM] using hrun

theorem positionSlotLoopTM_hoareTime_internal
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
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = positionSlotWorkAt work₀ sourceIdx counterIdx fuel ∧
        out = out₀)
      (positionSlotLoopTime fuel) := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  rw [hinp, hworkEq, hout]
  let final : Cfg n (positionSlotLoopTM sourceIdx counterIdx limitIdx).Q :=
    { state := (positionSlotLoopTM sourceIdx counterIdx limitIdx).qhalt
      input := inp₀
      work := positionSlotWorkAt work₀ sourceIdx counterIdx fuel
      output := out₀ }
  exact ⟨final, positionSlotLoopTime fuel, le_rfl,
    positionSlotLoopTM_reachesIn_frame_internal sourceIdx counterIdx limitIdx
      hsc hcl hsl slotValue fuel inp₀ work₀ out₀ hinput hslot hcounter hlimit
      hwork houtput,
    rfl, rfl, rfl, rfl⟩

private theorem positionSlotWorkAt_cfg_withinAuxSpace
    {Q : Type} (state : Q) (sourceIdx counterIdx : Fin n)
    (hsc : sourceIdx ≠ counterIdx)
    (fuel current inputLength initialSpace : ℕ) (hcurrent : current ≤ fuel)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hcounter : (work counterIdx).HasBinaryNat 0)
    (hworkSpace : ∀ i, (work i).head ≤ initialSpace)
    (hinputSpace : inp.head ≤ inputLength + initialSpace + 1) :
    ({ state := state
       input := inp
       work := positionSlotWorkAt work sourceIdx counterIdx current
       output := out } : Cfg n Q).WithinAuxSpace
      inputLength (initialSpace + 2 * fuel) := by
  constructor
  · intro i
    change (positionSlotWorkAt work sourceIdx counterIdx current i).head ≤
      initialSpace + 2 * fuel
    by_cases hic : i = counterIdx
    · subst i
      have hone : 1 ≤ initialSpace := by
        rw [← hcounter.2.1]
        exact hworkSpace counterIdx
      rw [(positionSlotWorkAt_counter work sourceIdx counterIdx current).2.1]
      omega
    by_cases his : i = sourceIdx
    · subst i
      rw [positionSlotWorkAt_source work sourceIdx counterIdx hsc]
      simp only [positionSlotTapeAt]
      have hsourceSpace := hworkSpace sourceIdx
      omega
    · rw [positionSlotWorkAt_other work sourceIdx counterIdx i his hic]
      exact le_trans (hworkSpace i) (by omega)
  · change inp.head ≤ inputLength + (initialSpace + 2 * fuel) + 1
    omega

private def positionSlotLoopSpaceSpec
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
    TM.BinaryForLoopSpaceSpec
      (positionSlotLoopSpec sourceIdx counterIdx limitIdx hsc hcl hsl
        slotValue fuel inp₀ work₀ out₀ hinput hslot hlimit hwork houtput)
      inputLength (positionSlotSpace initialSpace fuel) where
  testPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hstart :
        (positionSlotScanCfg sourceIdx counterIdx limitIdx inp₀ work₀ out₀
          current).WithinAuxSpace inputLength (initialSpace + 2 * fuel) := by
      simpa [positionSlotScanCfg] using
        positionSlotWorkAt_cfg_withinAuxSpace
          (positionSlotScanCfg sourceIdx counterIdx limitIdx inp₀ work₀ out₀
            current).state sourceIdx counterIdx hsc fuel current inputLength
          initialSpace hcurrent inp₀ work₀ out₀ hcounter hworkSpace hinputSpace
    have hreach' :
        (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn time
          (positionSlotScanCfg sourceIdx counterIdx limitIdx inp₀ work₀ out₀
            current) cfg := by
      simpa [positionSlotLoopSpec] using hreach
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [TM.binaryForCompareTime, positionSlotSpace] at htime ⊢
      omega)
  iterationPrefixWithin := by
    intro current time cfg hcurrent htime hreach
    have hcurrentLe : current ≤ fuel := Nat.le_of_lt hcurrent
    have hstart :
        (positionSlotIterationStartCfg sourceIdx counterIdx limitIdx inp₀
          work₀ out₀ current).WithinAuxSpace inputLength
            (initialSpace + 2 * fuel) := by
      simpa [positionSlotIterationStartCfg] using
        positionSlotWorkAt_cfg_withinAuxSpace
          (positionSlotIterationStartCfg sourceIdx counterIdx limitIdx inp₀
            work₀ out₀ current).state sourceIdx counterIdx hsc fuel current
          inputLength initialSpace hcurrentLe inp₀ work₀ out₀ hcounter
          hworkSpace hinputSpace
    have hreach' :
        (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn time
          (positionSlotIterationStartCfg sourceIdx counterIdx limitIdx inp₀
            work₀ out₀ current) cfg := by
      simpa [positionSlotLoopSpec] using hreach
    have hsucc := TM.binarySuccTime_le current
    have hsize := Nat.size_le_size hcurrentLe
    exact (hstart.reachesIn hreach').mono le_rfl (by
      simp [TM.binaryForIterationTime, positionSlotSpace] at htime ⊢
      omega)

private theorem positionSlotLoopTM_hoareSpace
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
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).HoareSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      inputLength (positionSlotSpace initialSpace fuel) := by
  intro inp work out hpre cfg hreach
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  subst inp
  subst work
  subst out
  obtain ⟨time, hreachIn⟩ :=
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).reaches_to_reachesIn
      hreach
  let spec := positionSlotLoopSpec sourceIdx counterIdx limitIdx hsc hcl hsl
    slotValue fuel inp₀ work₀ out₀ hinput hslot hlimit hwork houtput
  have hstart : spec.scanCfg 0 =
      { state := (positionSlotLoopTM sourceIdx counterIdx limitIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } := by
    dsimp only [spec, positionSlotLoopSpec, positionSlotScanCfg]
    rw [positionSlotWorkAt_zero_eq work₀ sourceIdx counterIdx hsc hcounter]
    rfl
  have hfull := spec.reachesIn fuel 0 (by omega)
  rw [hstart] at hfull
  have htime : time ≤ TM.binaryForLoopTime (fun _ => 2) fuel 0 fuel :=
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn_le_halt
      hreachIn hfull (by
        dsimp only [spec, positionSlotLoopSpec, positionSlotDoneCfg]
        rfl)
  have hreachSpec :
      (positionSlotLoopTM sourceIdx counterIdx limitIdx).reachesIn time
        (spec.scanCfg 0) cfg := by
    rw [hstart]
    exact hreachIn
  exact (positionSlotLoopSpaceSpec sourceIdx counterIdx limitIdx hsc hcl hsl
    slotValue fuel inputLength initialSpace inp₀ work₀ out₀ hinput hslot
    hcounter hlimit hwork houtput hworkSpace hinputSpace)
      |>.prefix_withinAuxSpace fuel 0 time cfg (by omega)
        (by simpa [spec] using hreachSpec) htime

theorem positionSlotLoopTM_hoareTimeSpace_internal
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
    (positionSlotLoopTM sourceIdx counterIdx limitIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = positionSlotWorkAt work₀ sourceIdx counterIdx fuel ∧
        out = out₀)
      (positionSlotLoopTime fuel) inputLength
      (positionSlotSpace initialSpace fuel) :=
  (positionSlotLoopTM_hoareTime_internal sourceIdx counterIdx limitIdx hsc hcl
    hsl slotValue fuel inp₀ work₀ out₀ hinput hslot hcounter hlimit hwork
    houtput).and_hoareSpace
      (positionSlotLoopTM_hoareSpace sourceIdx counterIdx limitIdx hsc hcl hsl
        slotValue fuel inputLength initialSpace inp₀ work₀ out₀ hinput hslot
        hcounter hlimit hwork houtput hworkSpace hinputSpace)

theorem positionSlotTM_hoareTime_frame_internal
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
        work = moveSlotRightWork sourceIdx
          (positionSlotWorkAt work₀ sourceIdx counterIdx fuel) ∧
        out = out₀)
      (positionSlotTime fuel) := by
  let positioned := positionSlotWorkAt work₀ sourceIdx counterIdx fuel
  have hpositionedRead : ∀ i, (positioned i).read ≠ Γ.start :=
    positionSlotWorkAt_read_ne_start work₀ sourceIdx counterIdx hsc slotValue
      fuel hslot hwork
  have hloop := positionSlotLoopTM_hoareTime_internal sourceIdx counterIdx
    limitIdx hsc hcl hsl slotValue fuel inp₀ work₀ out₀ hinput hslot hcounter
    hlimit hwork houtput
  have hmove := moveSlotRightTM_hoareTime_internal sourceIdx inp₀ positioned
    out₀ hinput hpositionedRead houtput
  have htransition : ∀ inp work out,
      (inp = inp₀ ∧ work = positioned ∧ out = out₀) →
      TM.transitionInput inp = inp₀ ∧
        (fun i => TM.transitionTape (work i)) = positioned ∧
        TM.transitionTape out = out₀ := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact TM.phaseTransition_eq_self_of_reads_ne_start hinput hpositionedRead
      houtput
  simpa [positionSlotTM, positionSlotTime, positioned] using
    TM.seqTM_hoareTime _ _ hloop htransition hmove

theorem positionSlotTM_hoareTime_internal
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
      (positionSlotTime fuel) := by
  have hframe := positionSlotTM_hoareTime_frame_internal sourceIdx counterIdx
    limitIdx hsc hcl hsl slotValue fuel inp₀ work₀ out₀ hinput hslot hcounter
    hlimit hwork houtput
  refine hframe.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    le_rfl
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp [moveSlotRightWork,
      positionSlotWorkAt_source work₀ sourceIdx counterIdx hsc,
      positionSlotTapeAt, Tape.move]
  · simp [moveSlotRightWork,
      positionSlotWorkAt_source work₀ sourceIdx counterIdx hsc,
      positionSlotTapeAt, Tape.move]
  · rw [moveSlotRightWork, Function.update_of_ne hsc.symm]
    exact positionSlotWorkAt_counter work₀ sourceIdx counterIdx fuel
  · rw [moveSlotRightWork, Function.update_of_ne hsl.symm,
      positionSlotWorkAt_other work₀ sourceIdx counterIdx limitIdx hsl.symm
        hcl.symm]
  · intro i his hic hil
    rw [moveSlotRightWork, Function.update_of_ne his,
      positionSlotWorkAt_other work₀ sourceIdx counterIdx i his hic]

theorem positionSlotTM_hoareTimeSpace_internal
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
      (positionSlotSpace initialSpace fuel) := by
  let positioned := positionSlotWorkAt work₀ sourceIdx counterIdx fuel
  have hpositionedRead : ∀ i, (positioned i).read ≠ Γ.start :=
    positionSlotWorkAt_read_ne_start work₀ sourceIdx counterIdx hsc slotValue
      fuel hslot hwork
  have hloop := positionSlotLoopTM_hoareTimeSpace_internal sourceIdx counterIdx
    limitIdx hsc hcl hsl slotValue fuel inputLength initialSpace inp₀ work₀
    out₀ hinput hslot hcounter hlimit hwork houtput hworkSpace hinputSpace
  have hpositionedWithin :
      ({ state := (moveSlotRightTM sourceIdx).qstart
         input := inp₀
         work := positioned
         output := out₀ } : Cfg n (moveSlotRightTM sourceIdx).Q)
        |>.WithinAuxSpace inputLength (initialSpace + 2 * fuel) := by
    exact positionSlotWorkAt_cfg_withinAuxSpace
      (moveSlotRightTM sourceIdx).qstart sourceIdx counterIdx hsc fuel fuel
      inputLength initialSpace le_rfl inp₀ work₀ out₀ hcounter hworkSpace
      hinputSpace
  have hmove := (moveSlotRightTM_hoareTime_internal sourceIdx inp₀ positioned
    out₀ hinput hpositionedRead houtput).toHoareTimeSpace (by
      rintro _ _ _ ⟨rfl, rfl, rfl⟩
      exact hpositionedWithin)
  have htransition : ∀ inp work out,
      (inp = inp₀ ∧ work = positioned ∧ out = out₀) →
      TM.transitionInput inp = inp₀ ∧
        (fun i => TM.transitionTape (work i)) = positioned ∧
        TM.transitionTape out = out₀ := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact TM.phaseTransition_eq_self_of_reads_ne_start hinput hpositionedRead
      houtput
  have hseq := TM.seqTM_hoareTimeSpace _ _ hloop htransition hmove
  refine hseq.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
    le_rfl le_rfl ?_
  · obtain ⟨rfl, rfl, rfl⟩ := h
    dsimp only [positioned]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp [moveSlotRightWork,
        positionSlotWorkAt_source work₀ sourceIdx counterIdx hsc,
        positionSlotTapeAt, Tape.move]
    · simp [moveSlotRightWork,
        positionSlotWorkAt_source work₀ sourceIdx counterIdx hsc,
        positionSlotTapeAt, Tape.move]
    · rw [moveSlotRightWork, Function.update_of_ne hsc.symm]
      exact positionSlotWorkAt_counter work₀ sourceIdx counterIdx fuel
    · rw [moveSlotRightWork, Function.update_of_ne hsl.symm,
        positionSlotWorkAt_other work₀ sourceIdx counterIdx limitIdx hsl.symm
          hcl.symm]
    · intro i his hic hil
      rw [moveSlotRightWork, Function.update_of_ne his,
        positionSlotWorkAt_other work₀ sourceIdx counterIdx i his hic]
  · simp [positionSlotSpace]
    omega

theorem moveSlotRightTM_hoareTimeSpace_internal
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
      1 inputLength (initialSpace + 1) := by
  apply (moveSlotRightTM_hoareTime_internal sourceIdx inp₀ work₀ out₀ hinput
    hwork houtput).toHoareTimeSpace
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  exact hinitial

theorem advanceSlotDigitTM_hoareTimeSpace_internal
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
      2 inputLength (initialSpace + 2) := by
  apply (advanceSlotDigitTM_hoareTime_internal sourceIdx inp₀ work₀ out₀ hinput
    hsourceNext hwork houtput).toHoareTimeSpace
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  exact hinitial

theorem moveSlotRightTM_isTransducer_internal (sourceIdx : Fin n) :
    (moveSlotRightTM sourceIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase <;> cases oHead <;>
    simp [moveSlotRightTM, TM.allIdle, TM.idleDir]

theorem advanceSlotDigitTM_isTransducer_internal (sourceIdx : Fin n) :
    (advanceSlotDigitTM sourceIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase <;> cases oHead <;>
    simp [advanceSlotDigitTM, TM.allIdle, TM.idleDir]

theorem positionSlotTM_isTransducer_internal
    (sourceIdx counterIdx limitIdx : Fin n) :
    (positionSlotTM sourceIdx counterIdx limitIdx).IsTransducer := by
  exact ((advanceSlotDigitTM_isTransducer_internal sourceIdx).binaryForTM
    counterIdx limitIdx).seqTM
      (moveSlotRightTM_isTransducer_internal sourceIdx)

end Machine

end BPCode

end Complexity
