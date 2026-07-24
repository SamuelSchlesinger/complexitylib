/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe
import Complexitylib.Models.TuringMachine.Placement
import Complexitylib.Models.TuringMachine.RetargetOutputFrame

/-!
# Restartable output probes with a real-output frame -- proof internals
-/

namespace Complexity

namespace TM

private theorem startInvariant_move_idle_parked (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    Parked (tape.move (idleDir tape.read)) := by
  constructor
  · by_cases hhead : tape.head = 0
    · have hread : tape.read = Γ.start := by
        simp [Tape.read, hhead, hinvariant.1]
      simp [Tape.move, idleDir, hread, hhead]
    · have hpositive : 1 ≤ tape.head := by omega
      have hread := hinvariant.read_ne_start hpositive
      simp [Tape.move, idleDir, hread]
      exact hpositive
  · intro index hindex
    simpa only [Tape.move_cells] using hinvariant.2 index hindex

private theorem startInvariant_writeAndMove_readBack_idle_parked (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    Parked (tape.writeAndMove (readBackWrite tape.read)
      (idleDir tape.read)) := by
  by_cases hread : tape.read = Γ.start
  · have hhead : tape.head = 0 := by
      by_contra hne
      exact hinvariant.read_ne_start (by omega) hread
    have hwrite : tape.write (readBackWrite tape.read) = tape := by
      simp [Tape.write, hhead]
    rw [show tape.writeAndMove (readBackWrite tape.read)
        (idleDir tape.read) = tape.move (idleDir tape.read) by
      simp only [Tape.writeAndMove, hwrite]]
    exact startInvariant_move_idle_parked tape hinvariant
  · rw [Tape.writeAndMove_readBack_idle_of_ne_start tape hread]
    exact ⟨by
      by_contra hhead
      exact hread (by simp [Tape.read, Nat.eq_zero_of_not_pos hhead,
        hinvariant.1]), hinvariant.2⟩

private theorem outputProbeCaptureCursor_ne_done {n : ℕ} {State : Type}
    (cursor : OutputCursor) :
    outputProbeCaptureCursor (n := n) (State := State) cursor ≠ .done := by
  cases cursor with
  | start => simp [outputProbeCaptureCursor]
  | cell symbol => cases symbol <;> simp [outputProbeCaptureCursor]

private theorem outputProbeAfterSourceTransition_ne_done {n : ℕ}
    {State : Type} (nextState : State) (cursor nextCursor : OutputCursor)
    (outputWrite : Γw) (outputDir : Dir3) (counterHead : Γ) :
    outputProbeAfterSourceTransition (n := n) nextState cursor nextCursor
      outputWrite outputDir counterHead ≠ .done := by
  cases cursor with
  | start =>
      unfold outputProbeAfterSourceTransition
      split <;> simp
  | cell symbol =>
      unfold outputProbeAfterSourceTransition
      split
      · simp_all
        by_cases hcounter : counterHead = Γ.blank
        · rw [if_pos hcounter]
          cases outputWrite <;> simp [outputProbeCaptureWrite]
        · rw [if_neg hcounter]
          simp
      · simp

private theorem outputProbeAfterPred_ne_done {n : ℕ} {State : Type}
    (sourceState : State) (cursor : OutputCursor)
    (mask : OutputProbeStartMask n) (phase : BinaryPredPhase) :
    outputProbeAfterPred sourceState cursor mask phase ≠ .done := by
  unfold outputProbeAfterPred
  split <;> simp

private theorem outputProbeNext_done_cases (tm : TM n)
    (phase : (outputProbeTM tm).Q) (inputHead : Γ)
    (workHeads : Fin (n + 1) → Γ) (outputHead : Γ)
    (hdone : ((outputProbeTM tm).δ phase inputHead workHeads outputHead).1 =
      (outputProbeTM tm).qhalt) :
    phase = .missing ∨
      (∃ bit, phase = .capture bit ∧ outputHead ≠ Γ.start) ∨
      phase = .done := by
  cases phase with
  | source state cursor =>
      simp only [outputProbeTM] at hdone
      split at hdone
      · split at hdone
        · exact (outputProbeCaptureCursor_ne_done cursor
            (by simpa [allReadBack] using hdone)).elim
        · simp [allReadBack] at hdone
      · exact (outputProbeAfterSourceTransition_ne_done _ _ _ _ _ _
          (by simpa [outputProbeSourceAction] using hdone)).elim
  | prepare state cursor =>
      simp [outputProbeTM, allReadBack] at hdone
  | pred state cursor mask predPhase =>
      exact (outputProbeAfterPred_ne_done state cursor mask _
        (by simpa [outputProbeTM] using hdone)).elim
  | restore state cursor mask =>
      simp [outputProbeTM] at hdone
  | capture bit =>
      right; left
      refine ⟨bit, rfl, ?_⟩
      intro hstart
      simp [outputProbeTM, hstart, allReadBack] at hdone
  | missing => exact Or.inl rfl
  | done => exact Or.inr (Or.inr rfl)

private theorem outputProbeTM_step_halted_parked_internal (tm : TM n)
    {before after : Cfg (n + 1) (outputProbeTM tm).Q}
    (hstep : (outputProbeTM tm).step before = some after)
    (hhalt : (outputProbeTM tm).halted after)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant) :
    Parked after.input ∧ ∀ i, Parked (after.work i) := by
  rcases before with ⟨phase, input, work, output⟩
  have hnotHalt : phase ≠ (outputProbeTM tm).qhalt :=
    state_ne_qhalt_of_step hstep
  have hdone :
      ((outputProbeTM tm).δ phase input.read (fun i => (work i).read)
        output.read).1 = (outputProbeTM tm).qhalt := by
    rw [TM.step, if_neg hnotHalt] at hstep
    generalize htransition :
        (outputProbeTM tm).δ phase input.read (fun i => (work i).read)
          output.read = transition at hstep ⊢
    obtain ⟨nextState, workWrites, outputWrite, inputDir, workDirs,
        outputDir⟩ := transition
    simp only [Option.some.injEq] at hstep
    exact (congrArg Cfg.state hstep).trans hhalt
  rcases outputProbeNext_done_cases tm phase input.read
      (fun i => (work i).read) output.read hdone with
    hmissing | hcapture | hdonePhase
  · subst phase
    have houtput : output.read ≠ Γ.start := by
      intro hstart
      simp [outputProbeTM, hstart, allReadBack] at hdone
    simp [TM.step, outputProbeTM, houtput] at hstep
    subst after
    exact ⟨startInvariant_move_idle_parked input hinput,
      fun i => startInvariant_writeAndMove_readBack_idle_parked
        (work i) (hwork i)⟩
  · obtain ⟨bit, hphase, houtput⟩ := hcapture
    subst phase
    simp [TM.step, outputProbeTM, houtput] at hstep
    subst after
    exact ⟨startInvariant_move_idle_parked input hinput,
      fun i => startInvariant_writeAndMove_readBack_idle_parked
        (work i) (hwork i)⟩
  · exact (hnotHalt hdonePhase).elim

private theorem startInvariant_reachesIn_internal (tm : TM n)
    {steps : ℕ} {start done : Cfg n tm.Q}
    (hreach : tm.reachesIn steps start done)
    (hinput : start.input.StartInvariant)
    (hwork : ∀ i, (start.work i).StartInvariant)
    (houtput : start.output.StartInvariant) :
    done.input.StartInvariant ∧
      (∀ i, (done.work i).StartInvariant) ∧
      done.output.StartInvariant := by
  induction hreach with
  | zero => exact ⟨hinput, hwork, houtput⟩
  | step hstep _ ih =>
      obtain ⟨hnextInput, hnextWork, hnextOutput⟩ :=
        Tape.StartInvariant.step tm hstep hinput hwork houtput
      exact ih hnextInput hnextWork hnextOutput

private theorem outputProbeTM_halted_reachesIn_parked_internal (tm : TM n)
    {steps : ℕ}
    {start done : Cfg (n + 1) (outputProbeTM tm).Q}
    (hreach : (outputProbeTM tm).reachesIn steps start done)
    (hhalt : (outputProbeTM tm).halted done)
    (hstartState : start.state ≠ (outputProbeTM tm).qhalt)
    (hinput : start.input.StartInvariant)
    (hwork : ∀ i, (start.work i).StartInvariant)
    (houtput : start.output.StartInvariant) :
    Parked done.input ∧ ∀ i, Parked (done.work i) := by
  have hsteps : steps ≠ 0 := by
    intro hzero
    subst steps
    cases hreach
    exact hstartState hhalt
  obtain ⟨priorSteps, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hsteps
  have hreach' : (outputProbeTM tm).reachesIn (priorSteps + 1)
      start done := by
    simpa using hreach
  obtain ⟨before, hprefix, hlast⟩ := reachesIn_split_internal hreach'
  obtain ⟨hbeforeInput, hbeforeWork, _hbeforeOutput⟩ :=
    startInvariant_reachesIn_internal (outputProbeTM tm) hprefix
      hinput hwork houtput
  cases hlast with
  | step hstep hzero =>
      cases hzero
      exact outputProbeTM_step_halted_parked_internal tm hstep hhalt
        hbeforeInput hbeforeWork

theorem
    ComputesInSpace.outputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (output : Tape) (houtput : Parked output) :
    ∃ probeSteps done,
      ((outputProbeStartedTM tm).retargetOutput).reachesIn probeSteps
        ((outputProbeStartedTM tm).retargetCfgFrame
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1))) output) done ∧
      ((outputProbeStartedTM tm).retargetOutput).halted done ∧
      (∃ bit, (done.work (Fin.last (n + 1))).HasOutput [bit]) ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      done.output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        ((outputProbeStartedTM tm).retargetOutput).reachesIn elapsed
          ((outputProbeStartedTM tm).retargetCfgFrame
            (outputProbeStartedCfg tm input
              (outputProbeCounterTape (index + 1))) output) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  obtain ⟨probeSteps, sourceDone, hsourceRun, hhalt, hout,
      hhead, hsourcePrefix⟩ :=
    hcomp.outputProbeStartedTM_index_halts_withinAuxSpace input index
  let sourceTM := outputProbeStartedTM tm
  let budget := outputProbeCaptureSpace (max 1 (space input.length))
    (index + 1)
  have hsourceTrans : sourceTM.IsTransducer :=
    (outputProbeTM_isTransducer tm).startedTM
  have hstartInput :
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).input.StartInvariant := by
    simpa [outputProbeStartedCfg] using
      (Tape.StartInvariant.init_ofBool input).move Dir3.right
  have hstartWork : ∀ i,
      ((outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).work i).StartInvariant := by
    intro i
    simp only [outputProbeStartedCfg]
    split
    · exact Tape.StartInvariant.init_nil.move Dir3.right
    · simpa [outputProbeCounterTape] using
        (Tape.StartInvariant.init_ofBool (index + 1).bits).move Dir3.right
  have hstartOutput :
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).output.StartInvariant := by
    simpa [outputProbeStartedCfg] using
      Tape.StartInvariant.init_nil.move Dir3.right
  have hsourceRunRaw :=
    (outputProbeTM tm).source_reachesIn_of_startedTM hsourceRun
  have hsourceStartState :
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).state ≠
        (outputProbeTM tm).qhalt := by
    have hprobeStart :
        (outputProbeTM tm).qstart ≠ (outputProbeTM tm).qhalt := by
      simp [outputProbeTM]
    rw [outputProbeStartedCfg,
      startedTM_qstart_eq_startedState (outputProbeTM tm) hprobeStart]
    intro hdone
    have hcases := outputProbeNext_done_cases tm
      (outputProbeTM tm).qstart Γ.start (fun _ => Γ.start) Γ.start
      (by simpa [startedState] using hdone)
    rcases hcases with hmissing | ⟨bit, hcapture, _⟩ | hhalted <;>
      simp [outputProbeTM] at *
  have hsourceParked :=
    outputProbeTM_halted_reachesIn_parked_internal tm hsourceRunRaw
      hhalt hsourceStartState hstartInput hstartWork hstartOutput
  have hsourceInvariants :=
    startInvariant_reachesIn_internal (outputProbeTM tm) hsourceRunRaw
      hstartInput hstartWork hstartOutput
  have hsourceOutputParked : Parked sourceDone.output := by
    refine ⟨?_, hsourceInvariants.2.2.2⟩
    rw [hhead]
    omega
  have hdoneOutput : sourceDone.output.head ≤ budget := by
    rw [hhead]
    dsimp only [budget, outputProbeCaptureSpace, outputProbeReplaySpace,
      outputProbePositiveSpace, binaryPredSpace]
    omega
  obtain ⟨hretargetRun, hretargetPrefix⟩ :=
    hsourceTrans.retargetOutput_reachesIn_retargetCfgFrame_withinAuxSpace
      output houtput hsourceRun hsourcePrefix hdoneOutput
  have hblankParked : ((Tape.init []).move Dir3.right).BlankAfter budget := by
    simpa only [Tape.BlankAfter, Tape.move_cells] using
      Tape.BlankAfter.init_nil budget
  have hstartBlank : ∀ i,
      ((sourceTM.retargetCfgFrame
        (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1))) output).work i).BlankAfter
        budget := by
    intro i
    by_cases hi : i.val < n + 1
    · rw [retargetCfgFrame_work_lt sourceTM _ output i hi]
      by_cases hsource : i.val < n
      · simpa [outputProbeStartedCfg, hsource] using hblankParked
      · have hilast : (⟨i.val, hi⟩ : Fin (n + 1)) = Fin.last n := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [hilast]
        have hcounterBlank :
            (outputProbeCounterTape (index + 1)).BlankAfter budget := by
          have hcounterNat :
              (outputProbeCounterTape (index + 1)).HasBinaryNat
                (index + 1) := by
            simpa [outputProbeCounterTape] using
              Tape.init_move_right_hasBinaryNat (index + 1)
          have hcontent : (outputProbeCounterTape
              (index + 1)).HasBinaryContent (index + 1).bits :=
            hcounterNat.2.2
          apply hcontent.blankAfter_of_length_le
          rw [Nat.size_eq_bits_len]
          have hsize := Nat.size_le_size
            (show index + 1 ≤ index + 1 + 1 by omega)
          dsimp only [budget, outputProbeCaptureSpace,
            outputProbeReplaySpace, outputProbePositiveSpace, binaryPredSpace]
          omega
        simpa [outputProbeStartedCfg] using hcounterBlank
    · have hilast : i = Fin.last (n + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      rw [retargetCfgFrame_work_last]
      simpa [outputProbeStartedCfg] using hblankParked
  let done := sourceTM.retargetCfgFrame sourceDone output
  have hdoneInputParked : Parked done.input := by
    simpa only [done, retargetCfgFrame_input] using hsourceParked.1
  have hdoneInputInvariant : done.input.StartInvariant := by
    simpa only [done, retargetCfgFrame_input] using hsourceInvariants.1
  have hdoneWorkParked : ∀ i, Parked (done.work i) := by
    intro i
    dsimp only [done]
    by_cases hi : i.val < n + 1
    · rw [retargetCfgFrame_work_lt sourceTM sourceDone output i hi]
      exact hsourceParked.2 ⟨i.val, hi⟩
    · have hilast : i = Fin.last (n + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      rw [retargetCfgFrame_work_last]
      exact hsourceOutputParked
  have hdoneWorkInvariant : ∀ i, (done.work i).StartInvariant := by
    intro i
    dsimp only [done]
    by_cases hi : i.val < n + 1
    · rw [retargetCfgFrame_work_lt sourceTM sourceDone output i hi]
      exact hsourceInvariants.2.1 ⟨i.val, hi⟩
    · have hilast : i = Fin.last (n + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      rw [retargetCfgFrame_work_last]
      exact hsourceInvariants.2.2
  refine ⟨probeSteps, done, hretargetRun, ?_, ?_, ?_, rfl,
    hdoneInputParked, hdoneInputInvariant, hdoneWorkParked, hdoneWorkInvariant,
    hretargetPrefix⟩
  · simpa only [done, retargetOutput_halted_retargetCfgFrame] using hhalt
  · obtain ⟨bit, hbit⟩ := hout
    refine ⟨bit, ?_⟩
    dsimp only [done]
    rw [retargetCfgFrame_work_last]
    exact hbit
  · intro i
    dsimp only [done]
    exact work_blankAfter_reachesIn i (hstartBlank i) hretargetRun
      hretargetPrefix

theorem ComputesInSpace.outputProbeStartedRetargetTM_getElem_withinAuxSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length)
    (output : Tape) (houtput : Parked output) :
    ∃ probeSteps done,
      ((outputProbeStartedTM tm).retargetOutput).reachesIn probeSteps
        ((outputProbeStartedTM tm).retargetCfgFrame
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1))) output) done ∧
      ((outputProbeStartedTM tm).retargetOutput).halted done ∧
      (done.work (Fin.last (n + 1))).HasOutput
        [(f input)[index]'hindex] ∧
      done.work ⟨n, by omega⟩ = outputProbeCounterTape 0 ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      done.output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        ((outputProbeStartedTM tm).retargetOutput).reachesIn elapsed
          ((outputProbeStartedTM tm).retargetCfgFrame
            (outputProbeStartedCfg tm input
              (outputProbeCounterTape (index + 1))) output) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  obtain ⟨probeSteps, sourceDone, hsourceRun, hhalt, hout, hcounter,
      hhead, hsourcePrefix⟩ :=
    hcomp.outputProbeStartedTM_getElem_withinAuxSpace input index hindex
  let sourceTM := outputProbeStartedTM tm
  let budget := outputProbeCaptureSpace (max 1 (space input.length))
    (index + 1)
  have hsourceTrans : sourceTM.IsTransducer :=
    (outputProbeTM_isTransducer tm).startedTM
  have hstartInput :
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).input.StartInvariant := by
    simpa [outputProbeStartedCfg] using
      (Tape.StartInvariant.init_ofBool input).move Dir3.right
  have hstartWork : ∀ i,
      ((outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).work i).StartInvariant := by
    intro i
    simp only [outputProbeStartedCfg]
    split
    · exact Tape.StartInvariant.init_nil.move Dir3.right
    · simpa [outputProbeCounterTape] using
        (Tape.StartInvariant.init_ofBool (index + 1).bits).move Dir3.right
  have hstartOutput :
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).output.StartInvariant := by
    simpa [outputProbeStartedCfg] using
      Tape.StartInvariant.init_nil.move Dir3.right
  have hsourceRunRaw :=
    (outputProbeTM tm).source_reachesIn_of_startedTM hsourceRun
  have hsourceStartState :
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))).state ≠
        (outputProbeTM tm).qhalt := by
    have hprobeStart :
        (outputProbeTM tm).qstart ≠ (outputProbeTM tm).qhalt := by
      simp [outputProbeTM]
    rw [outputProbeStartedCfg,
      startedTM_qstart_eq_startedState (outputProbeTM tm) hprobeStart]
    intro hdone
    have hcases := outputProbeNext_done_cases tm
      (outputProbeTM tm).qstart Γ.start (fun _ => Γ.start) Γ.start
      (by simpa [startedState] using hdone)
    rcases hcases with hmissing | ⟨bit, hcapture, _⟩ | hhalted <;>
      simp [outputProbeTM] at *
  have hsourceParked :=
    outputProbeTM_halted_reachesIn_parked_internal tm hsourceRunRaw
      hhalt hsourceStartState hstartInput hstartWork hstartOutput
  have hsourceInvariants :=
    startInvariant_reachesIn_internal (outputProbeTM tm) hsourceRunRaw
      hstartInput hstartWork hstartOutput
  have hsourceOutputParked : Parked sourceDone.output := by
    refine ⟨?_, hsourceInvariants.2.2.2⟩
    rw [hhead]
    omega
  have hdoneOutput : sourceDone.output.head ≤ budget := by
    rw [hhead]
    dsimp only [budget, outputProbeCaptureSpace, outputProbeReplaySpace,
      outputProbePositiveSpace, binaryPredSpace]
    omega
  obtain ⟨hretargetRun, hretargetPrefix⟩ :=
    hsourceTrans.retargetOutput_reachesIn_retargetCfgFrame_withinAuxSpace
      output houtput hsourceRun hsourcePrefix hdoneOutput
  have hblankParked : ((Tape.init []).move Dir3.right).BlankAfter budget := by
    simpa only [Tape.BlankAfter, Tape.move_cells] using
      Tape.BlankAfter.init_nil budget
  have hstartBlank : ∀ i,
      ((sourceTM.retargetCfgFrame
        (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1))) output).work i).BlankAfter
        budget := by
    intro i
    by_cases hi : i.val < n + 1
    · rw [retargetCfgFrame_work_lt sourceTM _ output i hi]
      by_cases hsource : i.val < n
      · simpa [outputProbeStartedCfg, hsource] using hblankParked
      · have hilast : (⟨i.val, hi⟩ : Fin (n + 1)) = Fin.last n := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [hilast]
        have hcounterBlank :
            (outputProbeCounterTape (index + 1)).BlankAfter budget := by
          have hcounterNat :
              (outputProbeCounterTape (index + 1)).HasBinaryNat
                (index + 1) := by
            simpa [outputProbeCounterTape] using
              Tape.init_move_right_hasBinaryNat (index + 1)
          have hcontent : (outputProbeCounterTape
              (index + 1)).HasBinaryContent (index + 1).bits :=
            hcounterNat.2.2
          apply hcontent.blankAfter_of_length_le
          rw [Nat.size_eq_bits_len]
          have hsize := Nat.size_le_size
            (show index + 1 ≤ index + 1 + 1 by omega)
          dsimp only [budget, outputProbeCaptureSpace,
            outputProbeReplaySpace, outputProbePositiveSpace, binaryPredSpace]
          omega
        simpa [outputProbeStartedCfg] using hcounterBlank
    · have hilast : i = Fin.last (n + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      rw [retargetCfgFrame_work_last]
      simpa [outputProbeStartedCfg] using hblankParked
  let done := sourceTM.retargetCfgFrame sourceDone output
  have hdoneInputParked : Parked done.input := by
    simpa only [done, retargetCfgFrame_input] using hsourceParked.1
  have hdoneInputInvariant : done.input.StartInvariant := by
    simpa only [done, retargetCfgFrame_input] using hsourceInvariants.1
  have hdoneWorkParked : ∀ i, Parked (done.work i) := by
    intro i
    dsimp only [done]
    by_cases hi : i.val < n + 1
    · rw [retargetCfgFrame_work_lt sourceTM sourceDone output i hi]
      exact hsourceParked.2 ⟨i.val, hi⟩
    · have hilast : i = Fin.last (n + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      rw [retargetCfgFrame_work_last]
      exact hsourceOutputParked
  have hdoneWorkInvariant : ∀ i, (done.work i).StartInvariant := by
    intro i
    dsimp only [done]
    by_cases hi : i.val < n + 1
    · rw [retargetCfgFrame_work_lt sourceTM sourceDone output i hi]
      exact hsourceInvariants.2.1 ⟨i.val, hi⟩
    · have hilast : i = Fin.last (n + 1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst i
      rw [retargetCfgFrame_work_last]
      exact hsourceInvariants.2.2
  refine ⟨probeSteps, done, hretargetRun, ?_, ?_, ?_, ?_, rfl,
    hdoneInputParked, hdoneInputInvariant, hdoneWorkParked, hdoneWorkInvariant,
    hretargetPrefix⟩
  · simpa only [done, retargetOutput_halted_retargetCfgFrame] using hhalt
  · dsimp only [done]
    rw [retargetCfgFrame_work_last]
    exact hout
  · dsimp only [done]
    rw [retargetCfgFrame_work_lt]
    exact hcounter
  · intro i
    dsimp only [done]
    exact work_blankAfter_reachesIn i (hstartBlank i) hretargetRun
      hretargetPrefix

theorem
    ComputesInSpace.placeOutputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (pre post : ℕ)
    (input : List Bool) (index : ℕ)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (pre + (n + 2) + post) → Tape)
    {frameSpace : ℕ}
    (hextra : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let start := (outputProbeStartedTM tm).retargetCfgFrame
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))) output
    ∃ probeSteps done,
      (placeWorkTM pre post queryTM).reachesIn probeSteps
        (placeWorkCfg queryTM pre post extras start)
        (placeWorkCfg queryTM pre post extras done) ∧
      (placeWorkTM pre post queryTM).halted
        (placeWorkCfg queryTM pre post extras done) ∧
      (∃ bit, ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post (Fin.last (n + 1)))).HasOutput [bit]) ∧
      (∀ i, ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post i)).BlankAfter
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1))) ∧
      (placeWorkCfg queryTM pre post extras done).output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (placeWorkTM pre post queryTM).reachesIn elapsed
          (placeWorkCfg queryTM pre post extras start) cfg →
        cfg.WithinAuxSpace input.length
          (max
            (outputProbeCaptureSpace (max 1 (space input.length))
              (index + 1))
            frameSpace) := by
  dsimp only
  obtain ⟨probeSteps, done, hreach, hhalt, hout, hblank,
      houtputDone, hinputParked, hinputInvariant, hworkParked,
      hworkInvariant, hprefix⟩ :=
    hcomp.outputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame_internal
      input index output houtput
  obtain ⟨hplaced, hplacedPrefix⟩ :=
    placeWorkTM_reachesIn_placeWorkCfg_stable_withinAuxSpace
      ((outputProbeStartedTM tm).retargetOutput) pre post extras hreach
      hextra hprefix hframe
  refine ⟨probeSteps, done, hplaced, hhalt, ?_, ?_, ?_, hinputParked,
    hinputInvariant, hworkParked, hworkInvariant, hplacedPrefix⟩
  · obtain ⟨bit, hbit⟩ := hout
    refine ⟨bit, ?_⟩
    rw [placeWorkCfg_work_middle]
    exact hbit
  · intro i
    rw [placeWorkCfg_work_middle]
    exact hblank i
  · simpa only [placeWorkCfg_output] using houtputDone

theorem ComputesInSpace.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (pre post : ℕ)
    (input : List Bool) (index : ℕ) (hindex : index < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (pre + (n + 2) + post) → Tape)
    {frameSpace : ℕ}
    (hextra : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let start := (outputProbeStartedTM tm).retargetCfgFrame
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1))) output
    ∃ probeSteps done,
      (placeWorkTM pre post queryTM).reachesIn probeSteps
        (placeWorkCfg queryTM pre post extras start)
        (placeWorkCfg queryTM pre post extras done) ∧
      (placeWorkTM pre post queryTM).halted
        (placeWorkCfg queryTM pre post extras done) ∧
      ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post (Fin.last (n + 1)))).HasOutput
          [(f input)[index]'hindex] ∧
      (placeWorkCfg queryTM pre post extras done).work
          (placeWorkIdx pre post ⟨n, by omega⟩) =
        outputProbeCounterTape 0 ∧
      (∀ i, ((placeWorkCfg queryTM pre post extras done).work
        (placeWorkIdx pre post i)).BlankAfter
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1))) ∧
      (placeWorkCfg queryTM pre post extras done).output = output ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (placeWorkTM pre post queryTM).reachesIn elapsed
          (placeWorkCfg queryTM pre post extras start) cfg →
        cfg.WithinAuxSpace input.length
          (max
            (outputProbeCaptureSpace (max 1 (space input.length))
              (index + 1))
            frameSpace) := by
  dsimp only
  obtain ⟨probeSteps, done, hreach, hhalt, hout, hcounter, hblank,
      houtputDone, hinputParked, hinputInvariant, hworkParked,
      hworkInvariant, hprefix⟩ :=
    hcomp.outputProbeStartedRetargetTM_getElem_withinAuxSpace_frame_internal
      input index hindex output houtput
  obtain ⟨hplaced, hplacedPrefix⟩ :=
    placeWorkTM_reachesIn_placeWorkCfg_stable_withinAuxSpace
      ((outputProbeStartedTM tm).retargetOutput) pre post extras hreach
      hextra hprefix hframe
  refine ⟨probeSteps, done, hplaced, ?_, ?_, ?_, ?_, ?_, hinputParked,
    hinputInvariant, hworkParked, hworkInvariant, hplacedPrefix⟩
  · exact hhalt
  · rw [placeWorkCfg_work_middle]
    exact hout
  · rw [placeWorkCfg_work_middle]
    exact hcounter
  · intro i
    rw [placeWorkCfg_work_middle]
    exact hblank i
  · simpa only [placeWorkCfg_output] using houtputDone

end TM

end Complexity
