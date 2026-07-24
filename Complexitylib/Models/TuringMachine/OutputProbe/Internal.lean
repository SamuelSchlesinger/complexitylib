/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe.Defs
import Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget
import Complexitylib.Models.TuringMachine.Combinators.WorkBranch
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Lift
import Complexitylib.Models.TuringMachine.Placement.Internal
import Complexitylib.Models.TuringMachine.SpaceTime.WorkSupport
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Random-access probes for append-only transducer output -- proof internals
-/

namespace Complexity

namespace TM

private theorem hasBinaryNat_positive_read_ne_blank_internal
    {tape : Tape} {value : ℕ} (hvalue : tape.HasBinaryNat value)
    (hpositive : 0 < value) : tape.read ≠ Γ.blank := by
  intro hblank
  have := hvalue.read_eq_blank_iff.mp hblank
  omega

theorem outputProbeCfg_sourceHeads_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) :
    outputProbeSourceHeads
      (fun i => ((outputProbeCfg tm cfg counter output).work i).read) =
      fun i => (cfg.work i).read := by
  funext i
  simp [outputProbeSourceHeads, outputProbeCfg]

@[simp] theorem outputProbeCfg_counter_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) :
    (outputProbeCfg tm cfg counter output).work
      (outputProbeCounterIdx n) = counter := by
  simp [outputProbeCfg, outputProbeCounterIdx]

theorem outputProbeTM_isTransducer_internal (tm : TM n) :
    (outputProbeTM tm).IsTransducer := by
  intro phase inputHead workHeads outputHead
  cases phase with
  | source sourceState cursor =>
      simp only [outputProbeTM]
      split
      · split <;> cases outputHead <;> simp [allReadBack, idleDir]
      · generalize htransition :
          tm.δ sourceState inputHead
            (outputProbeSourceHeads workHeads) cursor.read = transition
        obtain ⟨nextState, sourceWrites, outputWrite, inputDir,
          sourceDirs, outputDir⟩ := transition
        cases outputHead <;>
          simp [htransition, outputProbeSourceAction, idleDir]
  | prepare sourceState cursor =>
      cases outputHead <;> simp [outputProbeTM, allReadBack, idleDir]
  | pred sourceState cursor mask predPhase =>
      simp only [outputProbeTM]
      generalize htransition :
        (binaryPredTM (outputProbeCounterIdx n)).δ predPhase inputHead
          workHeads outputHead = transition
      obtain ⟨nextPhase, workWrites, outputWrite, inputDir,
        workDirs, outputDir⟩ := transition
      have htrans := binaryPredTM_isTransducer
        (outputProbeCounterIdx n) predPhase inputHead workHeads outputHead
      rw [htransition] at htrans
      exact htrans
  | restore sourceState cursor mask =>
      cases outputHead <;>
        simp [outputProbeTM, outputProbeRestoreDir, idleDir]
  | capture bit =>
      simp only [outputProbeTM]
      split
      · cases outputHead <;> simp [allReadBack, idleDir]
      · cases bit <;> simp
  | missing =>
      cases outputHead <;> simp [outputProbeTM, allReadBack, idleDir]
  | done =>
      cases outputHead <;> simp [outputProbeTM, allIdle, idleDir]

theorem outputProbeTM_step_source_internal (tm : TM n)
    {cfg cfg' : CursorCfg n tm.Q} (counter output : Tape)
    (hcounter : counter.read ≠ Γ.start)
    (hcursor : tm.cursorStep cfg = some cfg') :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeSourceResultCfg tm cfg cfg' counter
        (suppressOutputTapeStep output)) := by
  by_cases hhalt : cfg.state = tm.qhalt
  · simp [cursorStep, hhalt] at hcursor
  · generalize htransition :
      tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
        cfg.output.read = transition
    obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
      outputDir⟩ := transition
    simp only [cursorStep, hhalt, if_false, htransition,
      Option.some.injEq] at hcursor
    subst cfg'
    have hheads :
        outputProbeSourceHeads
          (fun i =>
            ((if h : i.val < n then cfg.work ⟨i.val, h⟩
              else counter) : Tape).read) =
          fun i => (cfg.work i).read := by
      funext i
      simp [outputProbeSourceHeads]
    have hcounterIdle :
        counter.writeAndMove (readBackWrite counter.read)
          (idleDir counter.read) = counter := by
      rw [writeAndMove_readBack counter hcounter]
      simp [idleDir, hcounter, Tape.move]
    simp [TM.step, outputProbeTM, outputProbeCfg,
      outputProbeSourceResultCfg,
      outputProbeSourceWrites, outputProbeSourceDirs,
      outputProbeSourceAction, cursorOutputWrite, cursorOutputDirection,
      suppressOutputTapeStep, outputProbeCounterIdx, hhalt, hheads,
      htransition]
    funext i
    split
    · rfl
    · exact hcounterIdle

theorem outputProbeTM_step_pred_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor)
    (mask : OutputProbeStartMask n)
    {cfg cfg' : Cfg (n + 1)
      (binaryPredTM (outputProbeCounterIdx n)).Q}
    (hstep : (binaryPredTM (outputProbeCounterIdx n)).step cfg =
      some cfg') :
    (outputProbeTM tm).step
      (outputProbePredCfg tm sourceState cursor mask cfg) =
      some (outputProbePredCfg tm sourceState cursor mask cfg') := by
  have hstate : cfg.state ≠ BinaryPredPhase.done := by
    exact state_ne_qhalt_of_step hstep
  have hhalt :
      cfg.state ≠ (binaryPredTM (outputProbeCounterIdx n)).qhalt :=
    hstate
  generalize htransition :
    (binaryPredTM (outputProbeCounterIdx n)).δ cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read = transition
  obtain ⟨nextPhase, workWrites, outputWrite, inputDir, workDirs,
    outputDir⟩ := transition
  rw [TM.step, if_neg hhalt, htransition] at hstep
  simp only [Option.some.injEq] at hstep
  subst cfg'
  have hcurrent : outputProbeAfterPred sourceState cursor mask cfg.state =
      .pred sourceState cursor mask cfg.state := by
    unfold outputProbeAfterPred
    exact if_neg hstate
  have hprobeNotHalt :
      (OutputProbeQ.pred sourceState cursor mask cfg.state :
        OutputProbeQ n tm.Q) ≠
        .done := by
    simp
  have hwrappedNotHalt :
      outputProbeAfterPred sourceState cursor mask cfg.state ≠
        (outputProbeTM tm).qhalt := by
    rw [hcurrent]
    exact hprobeNotHalt
  rw [TM.step]
  simp only [outputProbePredCfg, hcurrent]
  split
  · next heq => exact (hwrappedNotHalt heq).elim
  · simp only [outputProbeTM, htransition]

theorem outputProbeTM_reachesIn_pred_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor)
    (mask : OutputProbeStartMask n)
    {steps : ℕ}
    {cfg cfg' : Cfg (n + 1)
      (binaryPredTM (outputProbeCounterIdx n)).Q}
    (hreach : (binaryPredTM (outputProbeCounterIdx n)).reachesIn
      steps cfg cfg') :
    (outputProbeTM tm).reachesIn steps
      (outputProbePredCfg tm sourceState cursor mask cfg)
      (outputProbePredCfg tm sourceState cursor mask cfg') := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih =>
      exact .step
        (outputProbeTM_step_pred_internal tm sourceState cursor mask hstep) ih

private theorem startInvariant_read_eq_start_iff_internal (tape : Tape)
    (hinv : tape.StartInvariant) :
    tape.read = Γ.start ↔ tape.head = 0 := by
  constructor
  · intro hread
    by_contra hhead
    exact hinv.2 tape.head (by omega) (by simpa [Tape.read] using hread)
  · intro hhead
    simp [Tape.read, hhead, hinv.1]

private theorem outputProbeNormalizeTape_eq_self_internal {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    outputProbeNormalizeTape tape = tape := by
  rw [outputProbeNormalizeTape, writeAndMove_readBack tape hread]
  simp [idleDir, hread, Tape.move]

private theorem outputProbeNormalizeInput_eq_self_internal {input : Tape}
    (hread : input.read ≠ Γ.start) :
    outputProbeNormalizeInput input = input := by
  simp [outputProbeNormalizeInput, idleDir, hread, Tape.move]

private theorem outputProbeNormalizeTape_read_ne_start_internal {tape : Tape}
    (hinv : tape.StartInvariant) :
    (outputProbeNormalizeTape tape).read ≠ Γ.start := by
  by_cases hread : tape.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal tape hinv).mp hread
    have hnormalized : outputProbeNormalizeTape tape = tape.move .right := by
      unfold outputProbeNormalizeTape
      simp only [hread, readBackWrite, idleDir]
      change (tape.write Γ.blank).move Dir3.right = tape.move Dir3.right
      rw [show tape.write Γ.blank = tape by simp [Tape.write, hhead]]
    rw [hnormalized]
    exact (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
  · rw [outputProbeNormalizeTape_eq_self_internal hread]
    exact hread

private theorem outputProbeNormalizeInput_read_ne_start_internal {input : Tape}
    (hinv : input.StartInvariant) :
    (outputProbeNormalizeInput input).read ≠ Γ.start := by
  by_cases hread : input.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal input hinv).mp hread
    rw [show outputProbeNormalizeInput input = input.move .right by
      simp [outputProbeNormalizeInput, idleDir, hread]]
    exact (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
  · rw [outputProbeNormalizeInput_eq_self_internal hread]
    exact hread

private theorem suppressOutputTapeTrace_startInvariant_probe_internal
    (steps : ℕ) {tape : Tape} (hinv : tape.StartInvariant) :
    (suppressOutputTapeTrace steps tape).StartInvariant := by
  induction steps generalizing tape with
  | zero => exact hinv
  | succ steps ih =>
      exact ih (hinv.writeAndMove _ _)

private theorem outputProbeNormalize_suppress_init_head_internal
    (steps : ℕ) :
    (outputProbeNormalizeTape
      (suppressOutputTapeTrace steps (Tape.init []))).head = 1 := by
  cases steps with
  | zero =>
      change (outputProbeNormalizeTape (Tape.init [])).head = 1
      rfl
  | succ steps =>
      rw [suppressOutputTapeTrace_succ_init]
      rw [outputProbeNormalizeTape_eq_self_internal (by
        simp [Tape.read, Tape.move, Tape.init])]
      rfl

private theorem outputProbeNormalize_suppress_init_cells_internal
    (steps : ℕ) :
    (outputProbeNormalizeTape
      (suppressOutputTapeTrace steps (Tape.init []))).cells =
        (Tape.init []).cells := by
  cases steps with
  | zero =>
      change (outputProbeNormalizeTape (Tape.init [])).cells =
        (Tape.init []).cells
      rfl
  | succ steps =>
      rw [suppressOutputTapeTrace_succ_init]
      rw [outputProbeNormalizeTape_eq_self_internal (by
        simp [Tape.read, Tape.move, Tape.init])]
      rfl

private theorem outputProbeRestoreInput_normalize_internal {input : Tape}
    (hinv : input.StartInvariant) :
    outputProbeRestoreInput (input.read == Γ.start)
      (outputProbeNormalizeInput input) = input := by
  by_cases hread : input.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal input hinv).mp hread
    have hnormalized : outputProbeNormalizeInput input = input.move .right := by
      simp [outputProbeNormalizeInput, idleDir, hread]
    have hnormalizedRead : (input.move .right).read ≠ Γ.start :=
      (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
    simp only [hread, beq_self_eq_true, hnormalized,
      outputProbeRestoreInput]
    rw [show outputProbeRestoreDir true (input.move .right).read = .left by
      simp [outputProbeRestoreDir, hnormalizedRead]]
    apply Tape.ext
    · simp [Tape.move, hhead]
    · simp [Tape.move]
  · have hbeq : (input.read == Γ.start) = false := by
      exact beq_eq_false_iff_ne.mpr hread
    rw [hbeq, outputProbeNormalizeInput_eq_self_internal hread]
    simp [outputProbeRestoreInput, outputProbeRestoreDir, hread, Tape.move]

private theorem outputProbeRestoreTape_normalize_internal {tape : Tape}
    (hinv : tape.StartInvariant) :
    outputProbeRestoreTape (tape.read == Γ.start)
      (outputProbeNormalizeTape tape) = tape := by
  by_cases hread : tape.read = Γ.start
  · have hhead :=
      (startInvariant_read_eq_start_iff_internal tape hinv).mp hread
    have hnormalized : outputProbeNormalizeTape tape = tape.move .right := by
      unfold outputProbeNormalizeTape
      simp only [hread, readBackWrite, idleDir]
      change (tape.write Γ.blank).move Dir3.right = tape.move Dir3.right
      rw [show tape.write Γ.blank = tape by simp [Tape.write, hhead]]
    have hnormalizedRead : (tape.move .right).read ≠ Γ.start :=
      (hinv.move .right).read_ne_start (by simp [Tape.move, hhead])
    simp only [hread, beq_self_eq_true, hnormalized, outputProbeRestoreTape]
    rw [writeAndMove_readBack _ hnormalizedRead]
    rw [show outputProbeRestoreDir true (tape.move .right).read = .left by
      simp [outputProbeRestoreDir, hnormalizedRead]]
    apply Tape.ext
    · simp [Tape.move, hhead]
    · simp [Tape.move]
  · have hbeq : (tape.read == Γ.start) = false := by
      exact beq_eq_false_iff_ne.mpr hread
    rw [hbeq, outputProbeNormalizeTape_eq_self_internal hread,
      outputProbeRestoreTape, writeAndMove_readBack _ hread]
    simp [outputProbeRestoreDir, hread, Tape.move]

theorem outputProbeTM_step_prepare_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor) (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    (outputProbeTM tm).step
      (outputProbePrepareCfg tm sourceState cursor input work output) =
      some (outputProbePredCfg tm sourceState cursor
        (outputProbeCfgStartMask input work)
        (outputProbePredStartCfg input work output)) := by
  simp [TM.step, outputProbeTM, outputProbePrepareCfg,
    outputProbePredCfg, outputProbePredStartCfg,
    outputProbeCfgStartMask, outputProbeStartMask,
    outputProbeAfterPred, allReadBack, outputProbeNormalizeInput,
    outputProbeNormalizeTape]
  funext i
  rfl

theorem outputProbeTM_step_restore_internal (tm : TM n)
    (sourceState : tm.Q) (cursor : OutputCursor)
    (mask : OutputProbeStartMask n) (input : Tape)
    (work : Fin (n + 1) → Tape) (output : Tape) :
    (outputProbeTM tm).step
      (outputProbeRestoreCfg tm sourceState cursor mask input work output) =
      some
        { state := OutputProbeQ.source sourceState cursor
          input := outputProbeRestoreInput mask.input input
          work := outputProbeRestoreWork mask work
          output := outputProbeNormalizeTape output } := by
  simp only [TM.step, outputProbeTM, outputProbeRestoreCfg,
    outputProbeRestoreInput,
    outputProbeNormalizeTape, outputProbeRestoreWorkDirs]
  rw [if_neg (by simp)]
  congr 2
  funext i
  unfold outputProbeRestoreWork
  split <;> rfl

theorem outputProbeSourceResultCfg_positive_internal (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    {value : ℕ} (hcounter : counter.HasBinaryNat (value + 1)) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbePrepareCfg tm after.state after.output after.input
        (fun i =>
          if h : i.val < n then after.work ⟨i.val, h⟩ else counter)
        output := by
  apply Cfg.ext
  · cases houtput : before.output with
    | start =>
        simp [outputProbeSourceResultCfg, outputProbePrepareCfg,
          outputProbeAfterSourceTransition, hdir,
          houtput]
    | cell symbol =>
        have hnotblank : counter.read ≠ Γ.blank :=
          hasBinaryNat_positive_read_ne_blank_internal hcounter (by omega)
        simp [outputProbeSourceResultCfg, outputProbePrepareCfg,
          outputProbeAfterSourceTransition, hdir,
          houtput, hnotblank]
  · rfl
  · rfl
  · rfl

theorem outputProbeSourceResultCfg_not_right_internal (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (hdir : tm.cursorOutputDirection before ≠ Dir3.right) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbeCfg tm after counter output := by
  apply Cfg.ext
  · simp [outputProbeSourceResultCfg, outputProbeCfg,
      outputProbeAfterSourceTransition, hdir]
  · rfl
  · rfl
  · rfl

theorem outputProbeSourceResultCfg_capture_internal (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (bit : Bool) (symbol : Γ)
    (hcursor : before.output = .cell symbol)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    (hwrite : tm.cursorOutputWrite before =
      if bit then Γw.one else Γw.zero)
    (hcounter : counter.HasBinaryNat 0) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbeCaptureCfg tm bit after.input
        (fun i =>
          if h : i.val < n then after.work ⟨i.val, h⟩ else counter)
        output := by
  have hblank : counter.read = Γ.blank :=
    hcounter.read_eq_blank_iff.mpr rfl
  apply Cfg.ext
  · cases bit <;>
      simp [outputProbeSourceResultCfg, outputProbeCaptureCfg,
        outputProbeAfterSourceTransition, outputProbeCaptureWrite,
        hcursor, hdir, hwrite, hblank]
  · rfl
  · rfl
  · rfl

theorem outputProbeSourceResultCfg_missing_internal (tm : TM n)
    (before after : CursorCfg n tm.Q) (counter output : Tape)
    (symbol : Γ)
    (hcursor : before.output = .cell symbol)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    (hwrite : tm.cursorOutputWrite before = Γw.blank)
    (hcounter : counter.HasBinaryNat 0) :
    outputProbeSourceResultCfg tm before after counter output =
      outputProbeMissingCfg tm after.input
        (fun i =>
          if h : i.val < n then after.work ⟨i.val, h⟩ else counter)
        output := by
  have hblank : counter.read = Γ.blank :=
    hcounter.read_eq_blank_iff.mpr rfl
  apply Cfg.ext
  · simp [outputProbeSourceResultCfg, outputProbeMissingCfg,
      outputProbeAfterSourceTransition, outputProbeCaptureWrite,
      hcursor, hdir, hwrite, hblank]
  · rfl
  · rfl
  · rfl

theorem outputProbeTM_reachesIn_source_not_right_internal (tm : TM n)
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (hcursor : tm.cursorStep before = some after)
    (hdir : tm.cursorOutputDirection before ≠ Dir3.right)
    (hcounter : counter.read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after counter
        (suppressOutputTapeStep output)) := by
  have hstep := outputProbeTM_step_source_internal tm counter output
    hcounter hcursor
  rw [outputProbeSourceResultCfg_not_right_internal tm before after
    counter (suppressOutputTapeStep output) hdir] at hstep
  exact .step hstep .zero

theorem outputProbeTM_reachesIn_source_positive_internal (tm : TM n)
    {before after : CursorCfg n tm.Q} {value : ℕ}
    (counter output : Tape)
    (hcursor : tm.cursorStep before = some after)
    (hdir : tm.cursorOutputDirection before = Dir3.right)
    (hcounter : counter.HasBinaryNat (value + 1))
    (hinput : after.input.StartInvariant)
    (hwork : ∀ i, (after.work i).StartInvariant)
    (houtput : (suppressOutputTapeStep output).read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn (binaryPredTime value + 3)
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after (outputProbeCounterTape value)
        (suppressOutputTapeStep output)) := by
  let nextOutput := suppressOutputTapeStep output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩ else counter
  let mask := outputProbeCfgStartMask after.input framedWork
  let predStart := outputProbePredStartCfg after.input framedWork nextOutput
  have hcounterRead : counter.read ≠ Γ.start := by
    rw [Tape.read, hcounter.2.1]
    exact Tape.cells_ne_start_of_hasBinaryString hcounter.2 1 le_rfl
  have hcounterNormalized : outputProbeNormalizeTape counter = counter :=
    outputProbeNormalizeTape_eq_self_internal hcounterRead
  have hcounterAt :
      (predStart.work (outputProbeCounterIdx n)).HasBinaryNat
        (value + 1) := by
    simpa [predStart, outputProbePredStartCfg, outputProbeNormalizeWork,
      framedWork, outputProbeCounterIdx, hcounterNormalized] using hcounter
  have hother : ∀ i, i ≠ outputProbeCounterIdx n →
      (predStart.work i).read ≠ Γ.start := by
    intro i hi
    have hlt : i.val < n := by
      apply Fin.val_lt_last
      simpa [outputProbeCounterIdx] using hi
    simpa [predStart, outputProbePredStartCfg, outputProbeNormalizeWork,
      framedWork, hlt] using
      outputProbeNormalizeTape_read_ne_start_internal (hwork ⟨i.val, hlt⟩)
  obtain ⟨predFinal, hpredRun, hpredHalt, hpredInput,
    hpredOther, hpredCounter, hpredOutput⟩ :=
      binaryPredTM_reachesIn_frame (outputProbeCounterIdx n) value
        predStart.input predStart.work predStart.output hcounterAt
        (by
          simpa [predStart, outputProbePredStartCfg] using
            outputProbeNormalizeInput_read_ne_start_internal hinput)
        hother
        (by
          simpa [predStart, outputProbePredStartCfg, nextOutput,
            outputProbeNormalizeTape_eq_self_internal houtput] using houtput)
  have hfirst := outputProbeTM_step_source_internal tm counter output
    hcounterRead hcursor
  have hsourceResult :
      outputProbeSourceResultCfg tm before after counter nextOutput =
        outputProbePrepareCfg tm after.state after.output after.input
          framedWork nextOutput := by
    simpa [framedWork, nextOutput] using
      outputProbeSourceResultCfg_positive_internal tm before after
        counter nextOutput hdir hcounter
  have hprepare := outputProbeTM_step_prepare_internal tm after.state
    after.output after.input framedWork nextOutput
  have hprepareTarget :
      outputProbePredCfg tm after.state after.output mask predStart =
        outputProbePredCfg tm after.state after.output
          (outputProbeCfgStartMask after.input framedWork)
          (outputProbePredStartCfg after.input framedWork nextOutput) := by
    rfl
  rw [hprepareTarget] at hprepare
  have hwrappedRun := outputProbeTM_reachesIn_pred_internal tm
    after.state after.output mask hpredRun
  have hrestoreCfg :
      outputProbePredCfg tm after.state after.output mask predFinal =
        outputProbeRestoreCfg tm after.state after.output mask
          predFinal.input predFinal.work predFinal.output := by
    apply Cfg.ext
    · have hstate : predFinal.state = BinaryPredPhase.done := hpredHalt
      simp [outputProbePredCfg, outputProbeRestoreCfg, outputProbeAfterPred,
        hstate]
    · rfl
    · rfl
    · rfl
  have hrestore := outputProbeTM_step_restore_internal tm after.state
    after.output mask predFinal.input predFinal.work predFinal.output
  rw [← hrestoreCfg] at hrestore
  have hcounterEq :
      predFinal.work (outputProbeCounterIdx n) =
        outputProbeCounterTape value := by
    exact Tape.eq_init_move_right_of_hasBinaryString hpredCounter.2
      hpredCounter.1
  have hrestored :
      ({ state := OutputProbeQ.source after.state after.output
         input := outputProbeRestoreInput mask.input predFinal.input
         work := outputProbeRestoreWork mask predFinal.work
         output := outputProbeNormalizeTape predFinal.output } :
        Cfg (n + 1) (outputProbeTM tm).Q) =
      outputProbeCfg tm after (outputProbeCounterTape value) nextOutput := by
    apply Cfg.ext
    · rfl
    · rw [hpredInput]
      simpa [mask, predStart, outputProbePredStartCfg,
        outputProbeCfgStartMask, outputProbeStartMask] using
        outputProbeRestoreInput_normalize_internal hinput
    · change outputProbeRestoreWork mask predFinal.work =
        fun i =>
          if h : i.val < n then after.work ⟨i.val, h⟩
          else outputProbeCounterTape value
      funext i
      by_cases hi : i = outputProbeCounterIdx n
      · subst i
        have hcounterFinalRead :
            (outputProbeCounterTape value).read ≠ Γ.start := by
          rw [← hcounterEq]
          rw [Tape.read, hpredCounter.2.1]
          exact Tape.cells_ne_start_of_hasBinaryString hpredCounter.2 1 le_rfl
        have hlast : ¬ (outputProbeCounterIdx n).val < n := by
          simp [outputProbeCounterIdx]
        rw [show outputProbeRestoreWork mask predFinal.work
          (outputProbeCounterIdx n) = outputProbeNormalizeTape
            (predFinal.work (outputProbeCounterIdx n)) by
          simp [outputProbeRestoreWork, hlast], dif_neg hlast]
        rw [hcounterEq,
          outputProbeNormalizeTape_eq_self_internal hcounterFinalRead]
      · have hlt : i.val < n := by
          apply Fin.val_lt_last
          simpa [outputProbeCounterIdx] using hi
        have hsame := hpredOther i hi
        rw [dif_pos hlt]
        unfold outputProbeRestoreWork
        rw [dif_pos hlt]
        rw [hsame]
        have hmask : mask.work ⟨i.val, hlt⟩ =
            ((after.work ⟨i.val, hlt⟩).read == Γ.start) := by
          simp [mask, outputProbeCfgStartMask, outputProbeStartMask,
            outputProbeSourceHeads, framedWork]
        rw [hmask]
        simpa [predStart, outputProbePredStartCfg,
          outputProbeNormalizeWork, framedWork, hlt] using
          outputProbeRestoreTape_normalize_internal (hwork ⟨i.val, hlt⟩)
    · change outputProbeNormalizeTape predFinal.output = nextOutput
      rw [hpredOutput]
      change outputProbeNormalizeTape
        (outputProbeNormalizeTape nextOutput) = nextOutput
      rw [outputProbeNormalizeTape_eq_self_internal houtput,
        outputProbeNormalizeTape_eq_self_internal houtput]
  rw [hsourceResult] at hfirst
  rw [hrestored] at hrestore
  have hpredAndRestore :=
    (outputProbeTM tm).reachesIn_snoc hwrappedRun hrestore
  have hrun := TM.reachesIn.step hfirst
    (TM.reachesIn.step hprepare hpredAndRestore)
  have htime : binaryPredTime value + 1 + 1 + 1 =
      binaryPredTime value + 3 := by omega
  rw [← htime]
  simpa [nextOutput] using hrun

/-- Every prefix of one positive-countdown source invocation stays within the
explicit binary-width budget. This formulation is independent of the exact
phase reached by the prefix, so it composes directly across observed runs. -/
theorem outputProbeTM_source_positive_prefix_withinAuxSpace_internal
    (tm : TM n) {value inputLength initialSpace elapsed : ℕ}
    {before : CursorCfg n tm.Q} (counter output : Tape)
    {cfg : Cfg (n + 1) (outputProbeTM tm).Q}
    (hinitial :
      (outputProbeCfg tm before counter output).WithinAuxSpace
        inputLength initialSpace)
    (hprefix : elapsed ≤ binaryPredTime value + 3)
    (hreach : (outputProbeTM tm).reachesIn elapsed
      (outputProbeCfg tm before counter output) cfg) :
    cfg.WithinAuxSpace inputLength
      (outputProbePositiveSpace initialSpace value) := by
  have hspace := hinitial.reachesIn hreach
  apply hspace.mono le_rfl
  have htime := binaryPredTime_le value
  simp only [outputProbePositiveSpace, binaryPredSpace]
  omega

private theorem cursorStep_startInvariant_internal (tm : TM n)
    {before after : CursorCfg n tm.Q}
    (hstep : tm.cursorStep before = some after)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant) :
    after.input.StartInvariant ∧
      ∀ i, (after.work i).StartInvariant := by
  by_cases hhalt : before.state = tm.qhalt
  · simp [cursorStep, hhalt] at hstep
  · generalize htransition :
      tm.δ before.state before.input.read
        (fun i => (before.work i).read) before.output.read = transition
    obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
      outputDir⟩ := transition
    simp only [cursorStep, hhalt, if_false, htransition,
      Option.some.injEq] at hstep
    subst after
    exact ⟨hinput.move inputDir,
      fun i => (hwork i).writeAndMove (workWrites i) (workDirs i)⟩

private theorem suppressOutputTapeStep_startInvariant_internal {output : Tape}
    (hinv : output.StartInvariant) :
    (suppressOutputTapeStep output).StartInvariant :=
  hinv.writeAndMove _ _

private theorem suppressOutputTapeStep_read_ne_start_internal {output : Tape}
    (hinv : output.StartInvariant) :
    (suppressOutputTapeStep output).read ≠ Γ.start := by
  simpa [suppressOutputTapeStep, outputProbeNormalizeTape] using
    outputProbeNormalizeTape_read_ne_start_internal hinv

private theorem outputProbeCounterTape_hasBinaryNat_internal (value : ℕ) :
    (outputProbeCounterTape value).HasBinaryNat value := by
  simpa [outputProbeCounterTape] using Tape.init_move_right_hasBinaryNat value

theorem IsTransducer.outputProbeTM_step_startedCfg_internal
    {tm : TM n} (htrans : tm.IsTransducer) (input : List Bool)
    (value : ℕ) (hne : tm.qstart ≠ tm.qhalt) :
    (outputProbeTM tm).step
      (outputProbeCfg tm (.ofCfg (tm.initCfg input))
        (outputProbeCounterTape value) (Tape.init [])) =
      some (outputProbeStartedCfg tm input
        (outputProbeCounterTape value)) := by
  let sourceStarted := startedCfg tm input hne
  have hsourceStep : tm.step (tm.initCfg input) = some sourceStarted :=
    step_initCfg_startedCfg tm input hne
  have hcursorStep : tm.cursorStep (.ofCfg (tm.initCfg input)) =
      some (.ofCfg sourceStarted) :=
    htrans.cursorStep_commute Tape.StartInvariant.init_nil
      Tape.BlankAfterHead.init_nil hsourceStep
  have hcounter := outputProbeCounterTape_hasBinaryNat_internal value
  have hcounterRead : (outputProbeCounterTape value).read ≠ Γ.start := by
    rw [Tape.read, hcounter.2.1]
    exact Tape.cells_ne_start_of_hasBinaryString hcounter.2 1 le_rfl
  have hprobeStep := outputProbeTM_step_source_internal tm
    (outputProbeCounterTape value) (Tape.init []) hcounterRead hcursorStep
  rw [hprobeStep]
  apply congrArg some
  apply Cfg.ext
  · have hsourceState : sourceStarted.state = tm.startedState := by
      simp [sourceStarted, startedCfg, TM.step, hne, startedState,
        Tape.read, Tape.init]
    have hsourceOutput : sourceStarted.output.outputCursor =
        OutputCursor.cell Γ.blank := by
      rw [startedCfg_output_eq_init_move_right tm input hne]
      rfl
    have hdir : tm.cursorOutputDirection (.ofCfg (tm.initCfg input)) =
        Dir3.right := by
      apply cursorOutputDirection_eq_right_of_output_head_lt
        Tape.StartInvariant.init_nil hsourceStep
      rw [startedCfg_output_eq_init_move_right tm input hne]
      simp [Tape.move]
    have hstartOutputDir :
        (tm.δ tm.qstart Γ.start (fun _ => Γ.start) Γ.start).2.2.2.2.2 =
          Dir3.right := by
      exact (tm.δ_right_of_start tm.qstart Γ.start
        (fun _ => Γ.start) Γ.start).2.2 rfl
    have hstartHeads :
        outputProbeSourceHeads (n := n) (fun _ => Γ.start) =
          (fun _ => Γ.start) := by
      rfl
    have hprobeNe :
        (outputProbeTM tm).qstart ≠ (outputProbeTM tm).qhalt := by
      intro h
      cases h
    rw [show (outputProbeStartedCfg tm input
      (outputProbeCounterTape value)).state =
        (outputProbeStartedTM tm).qstart from rfl]
    rw [startedTM_qstart_eq_startedState (outputProbeTM tm) hprobeNe]
    simp only [outputProbeSourceResultCfg]
    rw [hdir]
    dsimp only [CursorCfg.ofCfg]
    rw [hsourceState, hsourceOutput]
    simp [startedState, outputProbeTM, outputProbeAfterSourceTransition,
      outputProbeSourceAction, OutputCursor.read, OutputCursor.next,
      Tape.outputCursor, hstartHeads, hstartOutputDir, hne, Tape.init]
  · rw [show (outputProbeSourceResultCfg tm
      (.ofCfg (tm.initCfg input)) (.ofCfg sourceStarted)
      (outputProbeCounterTape value)
      (suppressOutputTapeStep (Tape.init []))).input =
        sourceStarted.input from rfl]
    exact startedCfg_input_eq tm input hne
  · funext i
    by_cases hi : i.val < n
    · rw [show (outputProbeSourceResultCfg tm
        (.ofCfg (tm.initCfg input)) (.ofCfg sourceStarted)
      (outputProbeCounterTape value)
      (suppressOutputTapeStep (Tape.init []))).work i =
          sourceStarted.work ⟨i.val, hi⟩ by
          simp [outputProbeSourceResultCfg, CursorCfg.ofCfg, hi]]
      rw [startedCfg_work_eq_init_move_right tm input hne]
      simp [outputProbeStartedCfg, hi]
    · simp [outputProbeSourceResultCfg, outputProbeStartedCfg, hi]
  · change suppressOutputTapeStep (Tape.init []) =
      (Tape.init []).move Dir3.right
    simpa [suppressOutputTapeTrace] using suppressOutputTapeTrace_succ_init 0

private theorem outputProbeCfg_withinAuxSpace_internal (tm : TM n)
    {cfg : CursorCfg n tm.Q} {counter output : Tape}
    {inputLength sourceSpace : ℕ}
    (hwork : ∀ i, (cfg.work i).head ≤ sourceSpace)
    (hinput : cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hcounter : counter.head ≤ sourceSpace) :
    (outputProbeCfg tm cfg counter output).WithinAuxSpace
      inputLength sourceSpace := by
  constructor
  · intro i
    by_cases hi : i.val < n
    · simpa [outputProbeCfg, hi] using hwork ⟨i.val, hi⟩
    · simpa [outputProbeCfg, hi] using hcounter
  · simpa [outputProbeCfg] using hinput

/-- Simulate an entire observed cursor run while retaining `remaining`
uncrossed output cells in the countdown. The starting counter represents the
sum of `remaining` and all right moves in the source run; the final counter is
canonical `remaining`. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_internal (tm : TM n)
    {steps advances remaining : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat (remaining + advances))
    (houtput : output.StartInvariant) :
    ∃ probeSteps,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output)
        (outputProbeCfg tm after (outputProbeCounterTape remaining)
          (suppressOutputTapeTrace steps output)) := by
  induction steps generalizing before counter output advances with
  | zero =>
      simp only [cursorTraceObserved, Option.some.injEq,
        Prod.mk.injEq] at htrace
      obtain ⟨rfl, rfl⟩ := htrace
      refine ⟨0, ?_⟩
      have hcounterEq := hcounter.eq_init_move_right
      simpa [outputProbeCounterTape, hcounterEq] using
        (TM.reachesIn.zero :
          (outputProbeTM tm).reachesIn 0
            (outputProbeCfg tm before counter output)
            (outputProbeCfg tm before counter output))
  | succ steps ih =>
      cases hfirst : tm.cursorStep before with
      | none =>
          simp [cursorTraceObserved, cursorStepObserved, hfirst] at htrace
      | some next =>
          cases hlater : tm.cursorTraceObserved steps next with
          | none =>
              simp [cursorTraceObserved, cursorStepObserved, hfirst,
                hlater] at htrace
          | some result =>
              obtain ⟨final, later⟩ := result
              simp [cursorTraceObserved, cursorStepObserved, hfirst,
                hlater] at htrace
              obtain ⟨hfinal, hadvances⟩ := htrace
              subst after
              subst advances
              obtain ⟨hnextInput, hnextWork⟩ :=
                cursorStep_startInvariant_internal tm hfirst hinput hwork
              have hnextOutputInv :=
                suppressOutputTapeStep_startInvariant_internal houtput
              have hnextOutputRead :=
                suppressOutputTapeStep_read_ne_start_internal houtput
              by_cases hdir :
                  tm.cursorOutputDirection before = Dir3.right
              · have hadvance :
                    (tm.cursorOutputEvent before).advance = 1 := by
                  cases hdirection : tm.cursorOutputDirection before <;>
                    simp_all [cursorOutputEvent, OutputCursor.advanceCount]
                have hcounterPositive : counter.HasBinaryNat
                    ((remaining + later) + 1) := by
                  convert hcounter using 1
                  simp [hadvance]
                  omega
                have hsource :=
                  outputProbeTM_reachesIn_source_positive_internal tm
                    counter output hfirst hdir hcounterPositive hnextInput
                    hnextWork hnextOutputRead
                obtain ⟨laterSteps, hlaterRun⟩ := ih
                  (outputProbeCounterTape (remaining + later))
                  (suppressOutputTapeStep output) hlater hnextInput hnextWork
                  (outputProbeCounterTape_hasBinaryNat_internal
                    (remaining + later)) hnextOutputInv
                refine ⟨(binaryPredTime (remaining + later) + 3) +
                  laterSteps, ?_⟩
                simpa [suppressOutputTapeTrace] using
                  (outputProbeTM tm).reachesIn_trans hsource hlaterRun
              · have hadvance :
                    (tm.cursorOutputEvent before).advance = 0 := by
                  cases hdirection : tm.cursorOutputDirection before <;>
                    simp_all [cursorOutputEvent, OutputCursor.advanceCount]
                have hcounterSame :
                    counter.HasBinaryNat (remaining + later) := by
                  simpa [hadvance] using hcounter
                have hcounterRead : counter.read ≠ Γ.start := by
                  rw [Tape.read, hcounterSame.2.1]
                  exact Tape.cells_ne_start_of_hasBinaryString
                    hcounterSame.2 1 le_rfl
                have hsource :=
                  outputProbeTM_reachesIn_source_not_right_internal tm
                    counter output hfirst hdir hcounterRead
                obtain ⟨laterSteps, hlaterRun⟩ := ih counter
                  (suppressOutputTapeStep output) hlater hnextInput hnextWork
                  hcounterSame hnextOutputInv
                refine ⟨1 + laterSteps, ?_⟩
                simpa [suppressOutputTapeTrace] using
                  (outputProbeTM tm).reachesIn_trans hsource hlaterRun

/-- Replay an observed run with a uniform all-prefix auxiliary-space bound.
The abstract predicate `Inv` packages any source-machine invariant that is
preserved by cursor steps and bounds the source input/work heads. The extra
probe tape then costs only the binary width of `maxCounter`. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop)
    {steps advances remaining maxCounter inputLength sourceSpace : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinv : Inv before)
    (hinvStep : ∀ {cfg next}, Inv cfg →
      tm.cursorStep cfg = some next → Inv next)
    (hinvSpace : ∀ cfg, Inv cfg →
      (∀ i, (cfg.work i).head ≤ sourceSpace) ∧
      cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hsourceSpace : 1 ≤ sourceSpace)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat (remaining + advances))
    (houtput : output.StartInvariant)
    (hmax : remaining + advances ≤ maxCounter) :
    ∃ probeSteps,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output)
        (outputProbeCfg tm after (outputProbeCounterTape remaining)
          (suppressOutputTapeTrace steps output)) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeReplaySpace sourceSpace maxCounter) := by
  induction steps generalizing before counter output advances with
  | zero =>
      simp only [cursorTraceObserved, Option.some.injEq,
        Prod.mk.injEq] at htrace
      obtain ⟨rfl, rfl⟩ := htrace
      have hcounterHead : counter.head ≤ sourceSpace := by
        rw [hcounter.2.1]
        exact hsourceSpace
      have hinitial := outputProbeCfg_withinAuxSpace_internal
        (output := output) tm
        (hinvSpace before hinv).1 (hinvSpace before hinv).2 hcounterHead
      refine ⟨0, ?_, ?_⟩
      · have hcounterEq := hcounter.eq_init_move_right
        simpa [outputProbeCounterTape, hcounterEq] using
          (TM.reachesIn.zero :
            (outputProbeTM tm).reachesIn 0
              (outputProbeCfg tm before counter output)
              (outputProbeCfg tm before counter output))
      · intro elapsed cfg helapsed hreach
        have helapsedZero : elapsed = 0 := by omega
        subst elapsed
        have hcfg : cfg = outputProbeCfg tm before counter output :=
          (outputProbeTM tm).reachesIn_right_unique hreach .zero
        subst cfg
        exact hinitial.mono le_rfl (by
          simp [outputProbeReplaySpace, outputProbePositiveSpace,
            binaryPredSpace]
          omega)
  | succ steps ih =>
      cases hfirst : tm.cursorStep before with
      | none =>
          simp [cursorTraceObserved, cursorStepObserved, hfirst] at htrace
      | some next =>
          cases hlater : tm.cursorTraceObserved steps next with
          | none =>
              simp [cursorTraceObserved, cursorStepObserved, hfirst,
                hlater] at htrace
          | some result =>
              obtain ⟨final, later⟩ := result
              simp [cursorTraceObserved, cursorStepObserved, hfirst,
                hlater] at htrace
              obtain ⟨hfinal, hadvances⟩ := htrace
              subst after
              subst advances
              have hnextInv := hinvStep hinv hfirst
              obtain ⟨hnextInput, hnextWork⟩ :=
                cursorStep_startInvariant_internal tm hfirst hinput hwork
              have hnextOutputInv :=
                suppressOutputTapeStep_startInvariant_internal houtput
              have hnextOutputRead :=
                suppressOutputTapeStep_read_ne_start_internal houtput
              have hcounterHead : counter.head ≤ sourceSpace := by
                rw [hcounter.2.1]
                exact hsourceSpace
              have hinitial := outputProbeCfg_withinAuxSpace_internal
                (output := output) tm
                (hinvSpace before hinv).1 (hinvSpace before hinv).2
                hcounterHead
              by_cases hdir :
                  tm.cursorOutputDirection before = Dir3.right
              · have hadvance :
                    (tm.cursorOutputEvent before).advance = 1 := by
                  cases hdirection : tm.cursorOutputDirection before <;>
                    simp_all [cursorOutputEvent, OutputCursor.advanceCount]
                have hcounterPositive : counter.HasBinaryNat
                    ((remaining + later) + 1) := by
                  convert hcounter using 1
                  simp [hadvance]
                  omega
                have hvalueMax : remaining + later ≤ maxCounter := by
                  simp [hadvance] at hmax
                  omega
                have hsource :=
                  outputProbeTM_reachesIn_source_positive_internal tm
                    counter output hfirst hdir hcounterPositive hnextInput
                    hnextWork hnextOutputRead
                obtain ⟨laterSteps, hlaterRun, hlaterSpace⟩ := ih
                  (outputProbeCounterTape (remaining + later))
                  (suppressOutputTapeStep output) hlater hnextInv
                  hnextInput hnextWork
                  (outputProbeCounterTape_hasBinaryNat_internal
                    (remaining + later)) hnextOutputInv hvalueMax
                let firstSteps := binaryPredTime (remaining + later) + 3
                refine ⟨firstSteps + laterSteps, ?_, ?_⟩
                · simpa [firstSteps, suppressOutputTapeTrace] using
                    (outputProbeTM tm).reachesIn_trans hsource hlaterRun
                · intro elapsed cfg helapsed hreach
                  by_cases hwithinFirst : elapsed ≤ firstSteps
                  · have hlocal :=
                      outputProbeTM_source_positive_prefix_withinAuxSpace_internal
                        tm counter output hinitial (by
                          simpa [firstSteps] using hwithinFirst) hreach
                    apply hlocal.mono le_rfl
                    have hsize := Nat.size_le_size
                      (Nat.add_le_add_right hvalueMax 1)
                    simp only [outputProbeReplaySpace,
                      outputProbePositiveSpace, binaryPredSpace]
                    omega
                  · have hfirstLe : firstSteps ≤ elapsed := by omega
                    let tailSteps := elapsed - firstSteps
                    have htime : firstSteps + tailSteps = elapsed := by
                      dsimp only [tailSteps]
                      omega
                    rw [← htime] at hreach
                    obtain ⟨middle, hprefix, htail⟩ :=
                      reachesIn_split_internal hreach
                    have hmiddle : middle =
                        outputProbeCfg tm next
                          (outputProbeCounterTape (remaining + later))
                          (suppressOutputTapeStep output) :=
                      (outputProbeTM tm).reachesIn_right_unique hprefix
                        (by simpa [firstSteps] using hsource)
                    subst middle
                    apply hlaterSpace tailSteps cfg
                    · dsimp only [tailSteps]
                      omega
                    · exact htail

              · have hadvance :
                    (tm.cursorOutputEvent before).advance = 0 := by
                  cases hdirection : tm.cursorOutputDirection before <;>
                    simp_all [cursorOutputEvent, OutputCursor.advanceCount]
                have hcounterSame :
                    counter.HasBinaryNat (remaining + later) := by
                  simpa [hadvance] using hcounter
                have hcounterRead : counter.read ≠ Γ.start := by
                  rw [Tape.read, hcounterSame.2.1]
                  exact Tape.cells_ne_start_of_hasBinaryString
                    hcounterSame.2 1 le_rfl
                have hlaterMax : remaining + later ≤ maxCounter := by
                  simpa [hadvance] using hmax
                have hsource :=
                  outputProbeTM_reachesIn_source_not_right_internal tm
                    counter output hfirst hdir hcounterRead
                obtain ⟨laterSteps, hlaterRun, hlaterSpace⟩ := ih counter
                  (suppressOutputTapeStep output) hlater hnextInv
                  hnextInput hnextWork hcounterSame
                  hnextOutputInv hlaterMax
                refine ⟨1 + laterSteps, ?_, ?_⟩
                · simpa [suppressOutputTapeTrace] using
                    (outputProbeTM tm).reachesIn_trans hsource hlaterRun
                · intro elapsed cfg helapsed hreach
                  by_cases hwithinFirst : elapsed ≤ 1
                  · have hlocal := hinitial.reachesIn hreach
                    apply hlocal.mono le_rfl
                    simp [outputProbeReplaySpace,
                      outputProbePositiveSpace, binaryPredSpace]
                    omega
                  · have honeLe : 1 ≤ elapsed := by omega
                    let tailSteps := elapsed - 1
                    have htime : 1 + tailSteps = elapsed := by
                      dsimp only [tailSteps]
                      omega
                    rw [← htime] at hreach
                    obtain ⟨middle, hprefix, htail⟩ :=
                      reachesIn_split_internal hreach
                    have hmiddle : middle =
                        outputProbeCfg tm next counter
                          (suppressOutputTapeStep output) :=
                      (outputProbeTM tm).reachesIn_right_unique hprefix hsource
                    subst middle
                    apply hlaterSpace tailSteps cfg
                    · dsimp only [tailSteps]
                      omega
                    · exact htail

/-- Two post-replay capture transitions enlarge an all-prefix replay-space
bound by at most two cells. -/
private theorem outputProbeTM_captureTail_prefix_withinAuxSpace_internal
    (tm : TM n) {sourceSteps elapsed inputLength space : ℕ}
    {start middle done cfg : Cfg (n + 1) (outputProbeTM tm).Q}
    (hsource : (outputProbeTM tm).reachesIn sourceSteps start middle)
    (hsourceSpace : ∀ t c, t ≤ sourceSteps →
      (outputProbeTM tm).reachesIn t start c →
      c.WithinAuxSpace inputLength space)
    (_htail : (outputProbeTM tm).reachesIn 2 middle done)
    (helapsed : elapsed ≤ sourceSteps + 2)
    (hreach : (outputProbeTM tm).reachesIn elapsed start cfg) :
    cfg.WithinAuxSpace inputLength (space + 2) := by
  by_cases hbefore : elapsed ≤ sourceSteps
  · exact (hsourceSpace elapsed cfg hbefore hreach).mono le_rfl (by omega)
  · have hsourceLe : sourceSteps ≤ elapsed := by omega
    let tailSteps := elapsed - sourceSteps
    have helapsedEq : sourceSteps + tailSteps = elapsed := by
      dsimp only [tailSteps]
      omega
    rw [← helapsedEq] at hreach
    obtain ⟨replayEnd, hreplay, htailPrefix⟩ :=
      reachesIn_split_internal hreach
    have hreplayEnd : replayEnd = middle :=
      (outputProbeTM tm).reachesIn_right_unique hreplay hsource
    subst replayEnd
    have hmiddle := hsourceSpace sourceSteps middle le_rfl hsource
    have htailSteps : tailSteps ≤ 2 := by
      dsimp only [tailSteps]
      omega
    have htailWithin := hmiddle.reachesIn htailPrefix
    exact htailWithin.mono le_rfl (Nat.add_le_add_left htailSteps space)

theorem outputProbeTM_step_halt_capture_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) (bit : Bool)
    (hhalt : cfg.state = tm.qhalt)
    (hcursor : cfg.output = .cell (Γ.ofBool bit))
    (hcounter : counter.HasBinaryNat 0) :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeCaptureCfg tm bit
        (outputProbeNormalizeInput cfg.input)
        (outputProbeNormalizeWork fun i =>
          if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter)
        (outputProbeNormalizeTape output)) := by
  have hblank : counter.read = Γ.blank :=
    hcounter.read_eq_blank_iff.mpr rfl
  cases bit <;>
    simp [TM.step, outputProbeTM, outputProbeCfg, outputProbeCaptureCfg,
      outputProbeCaptureCursor, outputProbeNormalizeInput,
      outputProbeNormalizeTape, allReadBack, outputProbeCounterIdx,
      Γ.ofBool, hhalt, hcursor, hblank] <;>
    funext i <;> rfl

theorem outputProbeTM_step_halt_missing_zero_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape)
    (hhalt : cfg.state = tm.qhalt)
    (hcursor : (outputProbeCaptureCursor cfg.output :
      OutputProbeQ n tm.Q) = .missing)
    (hcounter : counter.HasBinaryNat 0) :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeMissingCfg tm
        (outputProbeNormalizeInput cfg.input)
        (outputProbeNormalizeWork fun i =>
          if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter)
        (outputProbeNormalizeTape output)) := by
  have hblank : counter.read = Γ.blank :=
    hcounter.read_eq_blank_iff.mpr rfl
  simp [TM.step, outputProbeTM, outputProbeCfg, outputProbeMissingCfg,
    outputProbeNormalizeInput, outputProbeNormalizeTape, allReadBack,
    outputProbeCounterIdx, hhalt, hcursor, hblank]
  funext i
  rfl

theorem outputProbeTM_step_halt_missing_positive_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) (remaining : ℕ)
    (hhalt : cfg.state = tm.qhalt)
    (hcounter : counter.HasBinaryNat (remaining + 1)) :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeMissingCfg tm
        (outputProbeNormalizeInput cfg.input)
        (outputProbeNormalizeWork fun i =>
          if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter)
        (outputProbeNormalizeTape output)) := by
  have hnotblank : counter.read ≠ Γ.blank := by
    intro hblank
    have hzero := hcounter.read_eq_blank_iff.mp hblank
    omega
  simp [TM.step, outputProbeTM, outputProbeCfg, outputProbeMissingCfg,
    outputProbeNormalizeInput,
    outputProbeNormalizeTape, allReadBack, outputProbeCounterIdx, hhalt,
    hnotblank]
  funext i
  rfl

theorem outputProbeTM_step_missing_internal (tm : TM n)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (houtput : output.read ≠ Γ.start) :
    (outputProbeTM tm).step
        (outputProbeMissingCfg tm input work output) =
      some (outputProbeMissingDoneCfg tm input work output) := by
  simp [TM.step, outputProbeTM, outputProbeMissingCfg,
    outputProbeMissingDoneCfg, houtput]

theorem outputProbeMissingDone_hasOutput_internal (tm : TM n)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (hhead : output.head = 1)
    (hcells : output.cells = (Tape.init []).cells) :
    (outputProbeMissingDoneCfg tm input work output).output.HasOutput
      [false] := by
  simp [outputProbeMissingDoneCfg, Tape.HasOutput, Tape.writeAndMove,
    Tape.write, Tape.move, hhead, hcells, Tape.init,
    Function.update_apply, Γ.ofBool]

theorem outputProbeMissingDone_head_internal (tm : TM n)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (hhead : output.head = 1) :
    (outputProbeMissingDoneCfg tm input work output).output.head = 2 := by
  simp [outputProbeMissingDoneCfg, Tape.writeAndMove, Tape.move,
    Tape.write_head, hhead]

/-- End-to-end termination when the source halts before the requested output
position. The positive residual countdown is preserved by the two terminal
read-back transitions. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_missing_positive_internal
    (tm : TM n) {steps advances remaining : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat ((remaining + 1) + advances))
    (houtput : output.StartInvariant)
    (hhalt : after.state = tm.qhalt)
    (hmissingHead :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).head = 1)
    (hmissingCells :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).cells =
          (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [false] := by
  obtain ⟨sourceSteps, hsourceRun⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_internal
      (remaining := remaining + 1) tm counter output htrace hinput hwork
      (by simpa [Nat.add_assoc] using hcounter) houtput
  let finalOutput := suppressOutputTapeTrace steps output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩
    else outputProbeCounterTape (remaining + 1)
  let missingInput := outputProbeNormalizeInput after.input
  let missingWork := outputProbeNormalizeWork framedWork
  let missingOutput := outputProbeNormalizeTape finalOutput
  let done := outputProbeMissingDoneCfg tm missingInput missingWork
    missingOutput
  have hhaltStep := outputProbeTM_step_halt_missing_positive_internal tm
    after (outputProbeCounterTape (remaining + 1)) finalOutput remaining
    hhalt (outputProbeCounterTape_hasBinaryNat_internal (remaining + 1))
  have hhaltStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm after (outputProbeCounterTape (remaining + 1))
          finalOutput) =
        some (outputProbeMissingCfg tm missingInput missingWork
          missingOutput) := by
    simpa [missingInput, missingWork, missingOutput, framedWork] using
      hhaltStep
  have hmissingRead : missingOutput.read ≠ Γ.start := by
    exact outputProbeNormalizeTape_read_ne_start_internal
      (suppressOutputTapeTrace_startInvariant_probe_internal steps houtput)
  have hmissingStep := outputProbeTM_step_missing_internal tm missingInput
    missingWork missingOutput hmissingRead
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm after (outputProbeCounterTape (remaining + 1))
        finalOutput) done := by
    simpa [done] using TM.reachesIn.step hhaltStep'
      (TM.reachesIn.step hmissingStep .zero)
  refine ⟨sourceSteps + 2, done, ?_, rfl, ?_⟩
  · exact (outputProbeTM tm).reachesIn_trans hsourceRun htail
  · exact outputProbeMissingDone_hasOutput_internal tm missingInput
      missingWork missingOutput hmissingHead hmissingCells

/-- The absent-position path retains the replay bound plus the two terminal
read-back transitions. -/
theorem
    outputProbeTM_reachesIn_cursorTraceObserved_missing_positive_withinAuxSpace_internal
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop) (sourceSpace : ℕ)
    {steps advances remaining maxCounter inputLength : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinv : Inv before)
    (hinvStep : ∀ {cfg next}, Inv cfg →
      tm.cursorStep cfg = some next → Inv next)
    (hinvSpace : ∀ cfg, Inv cfg →
      (∀ i, (cfg.work i).head ≤ sourceSpace) ∧
      cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hsourceSpace : 1 ≤ sourceSpace)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat ((remaining + 1) + advances))
    (houtput : output.StartInvariant)
    (hmax : (remaining + 1) + advances ≤ maxCounter)
    (hhalt : after.state = tm.qhalt)
    (hmissingHead :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).head = 1)
    (hmissingCells :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).cells =
          (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [false] ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeCaptureSpace sourceSpace maxCounter) := by
  obtain ⟨sourceSteps, hsourceRun, hsourcePrefix⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal
      (remaining := remaining + 1) tm Inv counter output htrace hinv
      hinvStep hinvSpace hsourceSpace hinput hwork
      (by simpa [Nat.add_assoc] using hcounter) houtput hmax
  let finalOutput := suppressOutputTapeTrace steps output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩
    else outputProbeCounterTape (remaining + 1)
  let missingInput := outputProbeNormalizeInput after.input
  let missingWork := outputProbeNormalizeWork framedWork
  let missingOutput := outputProbeNormalizeTape finalOutput
  let done := outputProbeMissingDoneCfg tm missingInput missingWork
    missingOutput
  have hhaltStep := outputProbeTM_step_halt_missing_positive_internal tm
    after (outputProbeCounterTape (remaining + 1)) finalOutput remaining
    hhalt (outputProbeCounterTape_hasBinaryNat_internal (remaining + 1))
  have hhaltStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm after (outputProbeCounterTape (remaining + 1))
          finalOutput) =
        some (outputProbeMissingCfg tm missingInput missingWork
          missingOutput) := by
    simpa [missingInput, missingWork, missingOutput, framedWork] using
      hhaltStep
  have hmissingRead : missingOutput.read ≠ Γ.start := by
    exact outputProbeNormalizeTape_read_ne_start_internal
      (suppressOutputTapeTrace_startInvariant_probe_internal steps houtput)
  have hmissingStep := outputProbeTM_step_missing_internal tm missingInput
    missingWork missingOutput hmissingRead
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm after (outputProbeCounterTape (remaining + 1))
        finalOutput) done := by
    simpa [done] using TM.reachesIn.step hhaltStep'
      (TM.reachesIn.step hmissingStep .zero)
  have hrun := (outputProbeTM tm).reachesIn_trans hsourceRun htail
  refine ⟨sourceSteps + 2, done, hrun, rfl, ?_, ?_, ?_⟩
  · exact outputProbeMissingDone_hasOutput_internal tm missingInput
      missingWork missingOutput hmissingHead hmissingCells
  · exact outputProbeMissingDone_head_internal tm missingInput missingWork
      missingOutput hmissingHead
  · intro elapsed cfg helapsed hprefix
    have hbound := outputProbeTM_captureTail_prefix_withinAuxSpace_internal
      tm hsourceRun hsourcePrefix htail helapsed hprefix
    simpa [outputProbeCaptureSpace] using hbound

/-- End-to-end termination when a zero countdown selects a non-Boolean source
frontier cell at halt. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_missing_zero_internal
    (tm : TM n) {steps advances : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hhalt : after.state = tm.qhalt)
    (hcursor : (outputProbeCaptureCursor after.output :
      OutputProbeQ n tm.Q) = .missing)
    (hmissingHead :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).head = 1)
    (hmissingCells :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).cells =
          (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [false] := by
  obtain ⟨sourceSteps, hsourceRun⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_internal
      (remaining := 0) tm counter output htrace hinput hwork
      (by simpa using hcounter) houtput
  let finalOutput := suppressOutputTapeTrace steps output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  let missingInput := outputProbeNormalizeInput after.input
  let missingWork := outputProbeNormalizeWork framedWork
  let missingOutput := outputProbeNormalizeTape finalOutput
  let done := outputProbeMissingDoneCfg tm missingInput missingWork
    missingOutput
  have hhaltStep := outputProbeTM_step_halt_missing_zero_internal tm after
    (outputProbeCounterTape 0) finalOutput hhalt hcursor
    (outputProbeCounterTape_hasBinaryNat_internal 0)
  have hhaltStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput) =
        some (outputProbeMissingCfg tm missingInput missingWork
          missingOutput) := by
    simpa [missingInput, missingWork, missingOutput, framedWork] using
      hhaltStep
  have hmissingRead : missingOutput.read ≠ Γ.start := by
    exact outputProbeNormalizeTape_read_ne_start_internal
      (suppressOutputTapeTrace_startInvariant_probe_internal steps houtput)
  have hmissingStep := outputProbeTM_step_missing_internal tm missingInput
    missingWork missingOutput hmissingRead
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput)
      done := by
    simpa [done] using TM.reachesIn.step hhaltStep'
      (TM.reachesIn.step hmissingStep .zero)
  refine ⟨sourceSteps + 2, done, ?_, rfl, ?_⟩
  · exact (outputProbeTM tm).reachesIn_trans hsourceRun htail
  · exact outputProbeMissingDone_hasOutput_internal tm missingInput
      missingWork missingOutput hmissingHead hmissingCells

/-- The halted non-Boolean frontier path uses the same replay-plus-two space
budget as successful capture. -/
theorem
    outputProbeTM_reachesIn_cursorTraceObserved_missing_zero_withinAuxSpace_internal
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop) (sourceSpace : ℕ)
    {steps advances maxCounter inputLength : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinv : Inv before)
    (hinvStep : ∀ {cfg next}, Inv cfg →
      tm.cursorStep cfg = some next → Inv next)
    (hinvSpace : ∀ cfg, Inv cfg →
      (∀ i, (cfg.work i).head ≤ sourceSpace) ∧
      cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hsourceSpace : 1 ≤ sourceSpace)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hmax : advances ≤ maxCounter)
    (hhalt : after.state = tm.qhalt)
    (hcursor : (outputProbeCaptureCursor after.output :
      OutputProbeQ n tm.Q) = .missing)
    (hmissingHead :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).head = 1)
    (hmissingCells :
      (outputProbeNormalizeTape
        (suppressOutputTapeTrace steps output)).cells =
          (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [false] ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeCaptureSpace sourceSpace maxCounter) := by
  obtain ⟨sourceSteps, hsourceRun, hsourcePrefix⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal
      (remaining := 0) tm Inv counter output htrace hinv hinvStep
      hinvSpace hsourceSpace hinput hwork (by simpa using hcounter)
      houtput (by simpa using hmax)
  let finalOutput := suppressOutputTapeTrace steps output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  let missingInput := outputProbeNormalizeInput after.input
  let missingWork := outputProbeNormalizeWork framedWork
  let missingOutput := outputProbeNormalizeTape finalOutput
  let done := outputProbeMissingDoneCfg tm missingInput missingWork
    missingOutput
  have hhaltStep := outputProbeTM_step_halt_missing_zero_internal tm after
    (outputProbeCounterTape 0) finalOutput hhalt hcursor
    (outputProbeCounterTape_hasBinaryNat_internal 0)
  have hhaltStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput) =
        some (outputProbeMissingCfg tm missingInput missingWork
          missingOutput) := by
    simpa [missingInput, missingWork, missingOutput, framedWork] using
      hhaltStep
  have hmissingRead : missingOutput.read ≠ Γ.start := by
    exact outputProbeNormalizeTape_read_ne_start_internal
      (suppressOutputTapeTrace_startInvariant_probe_internal steps houtput)
  have hmissingStep := outputProbeTM_step_missing_internal tm missingInput
    missingWork missingOutput hmissingRead
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput)
      done := by
    simpa [done] using TM.reachesIn.step hhaltStep'
      (TM.reachesIn.step hmissingStep .zero)
  have hrun := (outputProbeTM tm).reachesIn_trans hsourceRun htail
  refine ⟨sourceSteps + 2, done, hrun, rfl, ?_, ?_, ?_⟩
  · exact outputProbeMissingDone_hasOutput_internal tm missingInput
      missingWork missingOutput hmissingHead hmissingCells
  · exact outputProbeMissingDone_head_internal tm missingInput missingWork
      missingOutput hmissingHead
  · intro elapsed cfg helapsed hprefix
    have hbound := outputProbeTM_captureTail_prefix_withinAuxSpace_internal
      tm hsourceRun hsourcePrefix htail helapsed hprefix
    simpa [outputProbeCaptureSpace] using hbound

/-- The compulsory probe transition reaches the canonical restartable frame
even when the source machine is already halted at its start state. -/
theorem IsTransducer.outputProbeTM_step_startedCfg_total_internal
    {tm : TM n} (htrans : tm.IsTransducer) (input : List Bool)
    (value : ℕ) :
    (outputProbeTM tm).step
      (outputProbeCfg tm (.ofCfg (tm.initCfg input))
        (outputProbeCounterTape value) (Tape.init [])) =
      some (outputProbeStartedCfg tm input
        (outputProbeCounterTape value)) := by
  by_cases hne : tm.qstart ≠ tm.qhalt
  · exact htrans.outputProbeTM_step_startedCfg_internal input value hne
  · have hstart : tm.qstart = tm.qhalt := not_ne_iff.mp hne
    have hcounter := outputProbeCounterTape_hasBinaryNat_internal value
    have hcounterRead : (outputProbeCounterTape value).read ≠ Γ.start := by
      rw [Tape.read, hcounter.2.1]
      exact Tape.cells_ne_start_of_hasBinaryString hcounter.2 1 le_rfl
    have hprobeNe :
        (outputProbeTM tm).qstart ≠ (outputProbeTM tm).qhalt := by
      intro h
      cases h
    have hhalt : (CursorCfg.ofCfg (tm.initCfg input)).state = tm.qhalt := by
      simpa [CursorCfg.ofCfg, Cfg.init] using hstart
    have hstartedState :
        (outputProbeStartedCfg tm input
          (outputProbeCounterTape value)).state = .missing := by
      rw [show (outputProbeStartedCfg tm input
        (outputProbeCounterTape value)).state =
          (outputProbeStartedTM tm).qstart from rfl]
      rw [startedTM_qstart_eq_startedState (outputProbeTM tm) hprobeNe]
      simp [startedState, outputProbeTM, hstart, allReadBack]
    have hcounterNormalized :
        outputProbeNormalizeTape (outputProbeCounterTape value) =
          outputProbeCounterTape value :=
      outputProbeNormalizeTape_eq_self_internal hcounterRead
    have hnormalizeNil : outputProbeNormalizeTape (Tape.init []) =
        (Tape.init []).move Dir3.right := by
      rfl
    have hframe :
        outputProbeMissingCfg tm
          (outputProbeNormalizeInput
            (CursorCfg.ofCfg (tm.initCfg input)).input)
          (outputProbeNormalizeWork fun i =>
            if h : i.val < n then
              (CursorCfg.ofCfg (tm.initCfg input)).work ⟨i.val, h⟩
            else outputProbeCounterTape value)
          (outputProbeNormalizeTape (Tape.init [])) =
        outputProbeStartedCfg tm input
          (outputProbeCounterTape value) := by
      apply Cfg.ext
      · exact hstartedState.symm
      · rfl
      · funext i
        by_cases hi : i.val < n
        · simp only [outputProbeMissingCfg, outputProbeNormalizeWork,
            outputProbeStartedCfg, hi, ↓reduceDIte]
          change outputProbeNormalizeTape (Tape.init []) =
            (Tape.init []).move Dir3.right
          exact hnormalizeNil
        · simp only [outputProbeMissingCfg, outputProbeNormalizeWork,
            outputProbeStartedCfg, hi, ↓reduceDIte]
          change outputProbeNormalizeTape (outputProbeCounterTape value) =
            outputProbeCounterTape value
          exact hcounterNormalized
      · rfl
    cases value with
    | zero =>
        have hstep := outputProbeTM_step_halt_missing_zero_internal tm
          (.ofCfg (tm.initCfg input)) (outputProbeCounterTape 0)
          (Tape.init []) hhalt rfl
          (outputProbeCounterTape_hasBinaryNat_internal 0)
        rw [hframe] at hstep
        exact hstep
    | succ value =>
        have hstep := outputProbeTM_step_halt_missing_positive_internal tm
          (.ofCfg (tm.initCfg input)) (outputProbeCounterTape (value + 1))
          (Tape.init []) value hhalt
          (outputProbeCounterTape_hasBinaryNat_internal (value + 1))
        rw [hframe] at hstep
        exact hstep

theorem outputProbeTM_step_capture_internal (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (houtput : output.read ≠ Γ.start) :
    (outputProbeTM tm).step
      (outputProbeCaptureCfg tm bit input work output) =
      some (outputProbeDoneCfg tm bit input work output) := by
  cases bit <;>
    simp [TM.step, outputProbeTM, outputProbeCaptureCfg,
      outputProbeDoneCfg, houtput]

theorem outputProbeTM_capture_hasOutput_internal (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (hhead : output.head = 1)
    (hcells : output.cells = (Tape.init []).cells) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCaptureCfg tm bit input work output)
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeTM tm).halted
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeDoneCfg tm bit input work output).output.HasOutput [bit] := by
  have hread : output.read = Γ.blank := by
    rw [Tape.read, hhead, hcells]
    rfl
  refine ⟨TM.reachesIn.step
    (outputProbeTM_step_capture_internal tm bit input work output
      (by rw [hread]; decide)) .zero, rfl, ?_⟩
  cases bit <;>
    simp [outputProbeDoneCfg, Tape.HasOutput, Tape.writeAndMove,
      Tape.write, Tape.move, hhead, hcells, Tape.init,
      Function.update_apply, Γ.ofBool]

/-- End-to-end capture when an observed source run halts on the selected
Boolean frontier cell. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_capture_internal
    (tm : TM n) {steps advances : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape) (bit : Bool)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hhalt : after.state = tm.qhalt)
    (hcursor : after.output = .cell (Γ.ofBool bit))
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] := by
  obtain ⟨sourceSteps, hsourceRun⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_internal
      (remaining := 0) tm counter output htrace hinput hwork
      (by simpa using hcounter) houtput
  let finalOutput := suppressOutputTapeTrace steps output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  let captureInput := outputProbeNormalizeInput after.input
  let captureWork := outputProbeNormalizeWork framedWork
  have hhaltStep := outputProbeTM_step_halt_capture_internal tm after
    (outputProbeCounterTape 0) finalOutput bit hhalt hcursor
    (outputProbeCounterTape_hasBinaryNat_internal 0)
  have hfinalRead : finalOutput.read ≠ Γ.start := by
    rw [Tape.read, hphysicalHead]
    intro hstart
    rw [hphysicalCells] at hstart
    simp [Tape.init] at hstart
  have hfinalNormalize : outputProbeNormalizeTape finalOutput = finalOutput :=
    outputProbeNormalizeTape_eq_self_internal hfinalRead
  have hhaltStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput) =
        some (outputProbeCaptureCfg tm bit captureInput captureWork
          finalOutput) := by
    simpa [captureInput, captureWork, framedWork, hfinalNormalize] using
      hhaltStep
  obtain ⟨hcaptureRun, hdoneHalt, hdoneOutput⟩ :=
    outputProbeTM_capture_hasOutput_internal tm bit captureInput captureWork
      finalOutput hphysicalHead hphysicalCells
  let done := outputProbeDoneCfg tm bit captureInput captureWork finalOutput
  have htoCapture :=
    (outputProbeTM tm).reachesIn_snoc hsourceRun hhaltStep'
  have hrun := (outputProbeTM tm).reachesIn_trans htoCapture hcaptureRun
  refine ⟨sourceSteps + 2, done, ?_, ?_, ?_⟩
  · simpa [done, finalOutput, Nat.add_assoc] using hrun
  · simpa [done] using hdoneHalt
  · simpa [done] using hdoneOutput

/-- Space-aware end-to-end capture when an observed source run halts on the
selected Boolean frontier cell. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_capture_withinAuxSpace_internal
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop) (sourceSpace : ℕ)
    {steps advances inputLength : ℕ}
    {before after : CursorCfg n tm.Q} (counter output : Tape) (bit : Bool)
    (htrace : tm.cursorTraceObserved steps before = some (after, advances))
    (hinv : Inv before)
    (hinvStep : ∀ {cfg next}, Inv cfg →
      tm.cursorStep cfg = some next → Inv next)
    (hinvSpace : ∀ cfg, Inv cfg →
      (∀ i, (cfg.work i).head ≤ sourceSpace) ∧
      cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hsourceSpace : 1 ≤ sourceSpace)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hhalt : after.state = tm.qhalt)
    (hcursor : after.output = .cell (Γ.ofBool bit))
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] ∧
      done.work (Fin.last n) = outputProbeCounterTape 0 ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeCaptureSpace sourceSpace advances) := by
  obtain ⟨sourceSteps, hsourceRun, hsourcePrefix⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal
      (remaining := 0) (maxCounter := advances) tm Inv counter output
      htrace hinv hinvStep hinvSpace hsourceSpace hinput hwork
      (by simpa using hcounter) houtput (by omega)
  let finalOutput := suppressOutputTapeTrace steps output
  let framedWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then after.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  let captureInput := outputProbeNormalizeInput after.input
  let captureWork := outputProbeNormalizeWork framedWork
  have hhaltStep := outputProbeTM_step_halt_capture_internal tm after
    (outputProbeCounterTape 0) finalOutput bit hhalt hcursor
    (outputProbeCounterTape_hasBinaryNat_internal 0)
  have hfinalRead : finalOutput.read ≠ Γ.start := by
    rw [Tape.read, hphysicalHead]
    intro hstart
    rw [hphysicalCells] at hstart
    simp [Tape.init] at hstart
  have hfinalNormalize : outputProbeNormalizeTape finalOutput = finalOutput :=
    outputProbeNormalizeTape_eq_self_internal hfinalRead
  have hhaltStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput) =
        some (outputProbeCaptureCfg tm bit captureInput captureWork
          finalOutput) := by
    simpa [captureInput, captureWork, framedWork, hfinalNormalize] using
      hhaltStep
  obtain ⟨hcaptureRun, hdoneHalt, hdoneOutput⟩ :=
    outputProbeTM_capture_hasOutput_internal tm bit captureInput captureWork
      finalOutput hphysicalHead hphysicalCells
  let done := outputProbeDoneCfg tm bit captureInput captureWork finalOutput
  have htoCapture :=
    (outputProbeTM tm).reachesIn_snoc hsourceRun hhaltStep'
  have hrun := (outputProbeTM tm).reachesIn_trans htoCapture hcaptureRun
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm after (outputProbeCounterTape 0) finalOutput)
      done := by
    simpa [done, Nat.add_assoc] using
      (TM.reachesIn.step hhaltStep' hcaptureRun)
  refine ⟨sourceSteps + 2, done, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [done, finalOutput, Nat.add_assoc] using hrun
  · simpa [done] using hdoneHalt
  · simpa [done] using hdoneOutput
  · have hzero := outputProbeCounterTape_hasBinaryNat_internal 0
    have hzeroRead : (outputProbeCounterTape 0).read ≠ Γ.start := by
      rw [Tape.read, hzero.2.1]
      exact Tape.cells_ne_start_of_hasBinaryString hzero.2 1 le_rfl
    have hstable :
        (outputProbeNormalizeTape (outputProbeCounterTape 0)).writeAndMove
          (readBackWrite
            (outputProbeNormalizeTape (outputProbeCounterTape 0)).read)
          (idleDir
            (outputProbeNormalizeTape (outputProbeCounterTape 0)).read) =
          outputProbeCounterTape 0 := by
      rw [outputProbeNormalizeTape_eq_self_internal hzeroRead]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ hzeroRead
    simpa [done, outputProbeDoneCfg, captureWork,
      outputProbeNormalizeWork, framedWork] using hstable
  · have hfinalHead : finalOutput.head = 1 := by
      simpa [finalOutput] using hphysicalHead
    simp [done, outputProbeDoneCfg, Tape.writeAndMove, Tape.move,
      Tape.write_head, hfinalHead]
  · intro elapsed cfg helapsed hprefix
    have hbound := outputProbeTM_captureTail_prefix_withinAuxSpace_internal
      tm hsourceRun hsourcePrefix htail helapsed hprefix
    simpa [outputProbeCaptureSpace] using hbound

/-- End-to-end capture when the next source step finalizes the selected
Boolean cell by moving right. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_internal
    (tm : TM n) {steps advances : ℕ}
    {before selected next : CursorCfg n tm.Q}
    (counter output : Tape) (bit : Bool) (symbol : Γ)
    (htrace : tm.cursorTraceObserved steps before =
      some (selected, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hnext : tm.cursorStep selected = some next)
    (hcursor : selected.output = .cell symbol)
    (hdir : tm.cursorOutputDirection selected = Dir3.right)
    (hwrite : tm.cursorOutputWrite selected =
      if bit then Γw.one else Γw.zero)
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] := by
  obtain ⟨sourceSteps, hsourceRun⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_internal
      (remaining := 0) tm counter output htrace hinput hwork
      (by simpa using hcounter) houtput
  let finalOutput := suppressOutputTapeTrace steps output
  have hzero := outputProbeCounterTape_hasBinaryNat_internal 0
  have hzeroRead : (outputProbeCounterTape 0).read ≠ Γ.start := by
    rw [Tape.read, hzero.2.1]
    exact Tape.cells_ne_start_of_hasBinaryString hzero.2 1 le_rfl
  have hsourceStep := outputProbeTM_step_source_internal tm
    (outputProbeCounterTape 0) finalOutput hzeroRead hnext
  have hsourceCapture := outputProbeSourceResultCfg_capture_internal tm
    selected next (outputProbeCounterTape 0)
      (suppressOutputTapeStep finalOutput) bit symbol hcursor hdir hwrite hzero
  have hfinalRead : finalOutput.read ≠ Γ.start := by
    rw [Tape.read, hphysicalHead]
    intro hstart
    rw [hphysicalCells] at hstart
    simp [Tape.init] at hstart
  have hfinalStable : suppressOutputTapeStep finalOutput = finalOutput := by
    simpa [suppressOutputTapeStep, outputProbeNormalizeTape] using
      outputProbeNormalizeTape_eq_self_internal hfinalRead
  rw [hsourceCapture, hfinalStable] at hsourceStep
  let captureWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then next.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  obtain ⟨hcaptureRun, hdoneHalt, hdoneOutput⟩ :=
    outputProbeTM_capture_hasOutput_internal tm bit next.input captureWork
      finalOutput hphysicalHead hphysicalCells
  let done := outputProbeDoneCfg tm bit next.input captureWork finalOutput
  have htoCapture :=
    (outputProbeTM tm).reachesIn_snoc hsourceRun (by
      simpa [captureWork, finalOutput] using hsourceStep)
  have hrun := (outputProbeTM tm).reachesIn_trans htoCapture hcaptureRun
  refine ⟨sourceSteps + 2, done, ?_, ?_, ?_⟩
  · simpa [done, finalOutput, Nat.add_assoc] using hrun
  · simpa [done] using hdoneHalt
  · simpa [done] using hdoneOutput

/-- End-to-end termination when the next source step crosses the selected
cell while writing a blank symbol. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_finalize_missing_internal
    (tm : TM n) {steps advances : ℕ}
    {before selected next : CursorCfg n tm.Q}
    (counter output : Tape) (symbol : Γ)
    (htrace : tm.cursorTraceObserved steps before =
      some (selected, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hnext : tm.cursorStep selected = some next)
    (hcursor : selected.output = .cell symbol)
    (hdir : tm.cursorOutputDirection selected = Dir3.right)
    (hwrite : tm.cursorOutputWrite selected = Γw.blank)
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [false] := by
  obtain ⟨sourceSteps, hsourceRun⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_internal
      (remaining := 0) tm counter output htrace hinput hwork
      (by simpa using hcounter) houtput
  let finalOutput := suppressOutputTapeTrace steps output
  have hzero := outputProbeCounterTape_hasBinaryNat_internal 0
  have hzeroRead : (outputProbeCounterTape 0).read ≠ Γ.start := by
    rw [Tape.read, hzero.2.1]
    exact Tape.cells_ne_start_of_hasBinaryString hzero.2 1 le_rfl
  have hsourceStep := outputProbeTM_step_source_internal tm
    (outputProbeCounterTape 0) finalOutput hzeroRead hnext
  have hsourceMissing := outputProbeSourceResultCfg_missing_internal tm
    selected next (outputProbeCounterTape 0)
      (suppressOutputTapeStep finalOutput) symbol hcursor hdir hwrite hzero
  have hfinalRead : finalOutput.read ≠ Γ.start := by
    rw [Tape.read, hphysicalHead]
    intro hstart
    rw [hphysicalCells] at hstart
    simp [Tape.init] at hstart
  have hfinalStable : suppressOutputTapeStep finalOutput = finalOutput := by
    simpa [suppressOutputTapeStep, outputProbeNormalizeTape] using
      outputProbeNormalizeTape_eq_self_internal hfinalRead
  rw [hsourceMissing, hfinalStable] at hsourceStep
  let missingWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then next.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  let done := outputProbeMissingDoneCfg tm next.input missingWork finalOutput
  have hsourceStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm selected (outputProbeCounterTape 0)
          finalOutput) =
        some (outputProbeMissingCfg tm next.input missingWork
          finalOutput) := by
    simpa [missingWork, finalOutput] using hsourceStep
  have hmissingStep := outputProbeTM_step_missing_internal tm next.input
    missingWork finalOutput hfinalRead
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm selected (outputProbeCounterTape 0) finalOutput)
      done := by
    simpa [done] using TM.reachesIn.step hsourceStep'
      (TM.reachesIn.step hmissingStep .zero)
  refine ⟨sourceSteps + 2, done, ?_, rfl, ?_⟩
  · exact (outputProbeTM tm).reachesIn_trans hsourceRun htail
  · exact outputProbeMissingDone_hasOutput_internal tm next.input
      missingWork finalOutput hphysicalHead hphysicalCells

/-- Space-aware end-to-end capture when the next source step finalizes the
selected Boolean cell by moving right. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_withinAuxSpace_internal
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop) (sourceSpace : ℕ)
    {steps advances inputLength : ℕ}
    {before selected next : CursorCfg n tm.Q}
    (counter output : Tape) (bit : Bool) (symbol : Γ)
    (htrace : tm.cursorTraceObserved steps before =
      some (selected, advances))
    (hinv : Inv before)
    (hinvStep : ∀ {cfg next}, Inv cfg →
      tm.cursorStep cfg = some next → Inv next)
    (hinvSpace : ∀ cfg, Inv cfg →
      (∀ i, (cfg.work i).head ≤ sourceSpace) ∧
      cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hsourceSpace : 1 ≤ sourceSpace)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hnext : tm.cursorStep selected = some next)
    (hcursor : selected.output = .cell symbol)
    (hdir : tm.cursorOutputDirection selected = Dir3.right)
    (hwrite : tm.cursorOutputWrite selected =
      if bit then Γw.one else Γw.zero)
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] ∧
      done.work (Fin.last n) = outputProbeCounterTape 0 ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeCaptureSpace sourceSpace advances) := by
  obtain ⟨sourceSteps, hsourceRun, hsourcePrefix⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal
      (remaining := 0) (maxCounter := advances) tm Inv counter output
      htrace hinv hinvStep hinvSpace hsourceSpace hinput hwork
      (by simpa using hcounter) houtput (by omega)
  let finalOutput := suppressOutputTapeTrace steps output
  have hzero := outputProbeCounterTape_hasBinaryNat_internal 0
  have hzeroRead : (outputProbeCounterTape 0).read ≠ Γ.start := by
    rw [Tape.read, hzero.2.1]
    exact Tape.cells_ne_start_of_hasBinaryString hzero.2 1 le_rfl
  have hsourceStep := outputProbeTM_step_source_internal tm
    (outputProbeCounterTape 0) finalOutput hzeroRead hnext
  have hsourceCapture := outputProbeSourceResultCfg_capture_internal tm
    selected next (outputProbeCounterTape 0)
      (suppressOutputTapeStep finalOutput) bit symbol hcursor hdir hwrite hzero
  have hfinalRead : finalOutput.read ≠ Γ.start := by
    rw [Tape.read, hphysicalHead]
    intro hstart
    rw [hphysicalCells] at hstart
    simp [Tape.init] at hstart
  have hfinalStable : suppressOutputTapeStep finalOutput = finalOutput := by
    simpa [suppressOutputTapeStep, outputProbeNormalizeTape] using
      outputProbeNormalizeTape_eq_self_internal hfinalRead
  rw [hsourceCapture, hfinalStable] at hsourceStep
  let captureWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then next.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  have hsourceStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm selected (outputProbeCounterTape 0)
          finalOutput) =
        some (outputProbeCaptureCfg tm bit next.input captureWork
          finalOutput) := by
    simpa [captureWork, finalOutput] using hsourceStep
  obtain ⟨hcaptureRun, hdoneHalt, hdoneOutput⟩ :=
    outputProbeTM_capture_hasOutput_internal tm bit next.input captureWork
      finalOutput hphysicalHead hphysicalCells
  let done := outputProbeDoneCfg tm bit next.input captureWork finalOutput
  have htoCapture :=
    (outputProbeTM tm).reachesIn_snoc hsourceRun hsourceStep'
  have hrun := (outputProbeTM tm).reachesIn_trans htoCapture hcaptureRun
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm selected (outputProbeCounterTape 0) finalOutput)
      done := by
    simpa [done, Nat.add_assoc] using
      (TM.reachesIn.step hsourceStep' hcaptureRun)
  refine ⟨sourceSteps + 2, done, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [done, finalOutput, Nat.add_assoc] using hrun
  · simpa [done] using hdoneHalt
  · simpa [done] using hdoneOutput
  · have hstable :
        (outputProbeCounterTape 0).writeAndMove
          (readBackWrite (outputProbeCounterTape 0).read)
          (idleDir (outputProbeCounterTape 0).read) =
          outputProbeCounterTape 0 :=
      Tape.writeAndMove_readBack_idle_of_ne_start _ hzeroRead
    simpa [done, outputProbeDoneCfg, captureWork] using hstable
  · have hfinalHead : finalOutput.head = 1 := by
      simpa [finalOutput] using hphysicalHead
    simp [done, outputProbeDoneCfg, Tape.writeAndMove, Tape.move,
      Tape.write_head, hfinalHead]
  · intro elapsed cfg helapsed hprefix
    have hbound := outputProbeTM_captureTail_prefix_withinAuxSpace_internal
      tm hsourceRun hsourcePrefix htail helapsed hprefix
    simpa [outputProbeCaptureSpace] using hbound

/-- Space-aware termination when a right move finalizes the selected cell as
blank. -/
theorem
    outputProbeTM_reachesIn_cursorTraceObserved_finalize_missing_withinAuxSpace_internal
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop) (sourceSpace : ℕ)
    {steps advances maxCounter inputLength : ℕ}
    {before selected next : CursorCfg n tm.Q}
    (counter output : Tape) (symbol : Γ)
    (htrace : tm.cursorTraceObserved steps before =
      some (selected, advances))
    (hinv : Inv before)
    (hinvStep : ∀ {cfg next}, Inv cfg →
      tm.cursorStep cfg = some next → Inv next)
    (hinvSpace : ∀ cfg, Inv cfg →
      (∀ i, (cfg.work i).head ≤ sourceSpace) ∧
      cfg.input.head ≤ inputLength + sourceSpace + 1)
    (hsourceSpace : 1 ≤ sourceSpace)
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (houtput : output.StartInvariant)
    (hmax : advances ≤ maxCounter)
    (hnext : tm.cursorStep selected = some next)
    (hcursor : selected.output = .cell symbol)
    (hdir : tm.cursorOutputDirection selected = Dir3.right)
    (hwrite : tm.cursorOutputWrite selected = Γw.blank)
    (hphysicalHead : (suppressOutputTapeTrace steps output).head = 1)
    (hphysicalCells : (suppressOutputTapeTrace steps output).cells =
      (Tape.init []).cells) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [false] ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeCaptureSpace sourceSpace maxCounter) := by
  obtain ⟨sourceSteps, hsourceRun, hsourcePrefix⟩ :=
    outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal
      (remaining := 0) tm Inv counter output htrace hinv hinvStep
      hinvSpace hsourceSpace hinput hwork (by simpa using hcounter)
      houtput (by simpa using hmax)
  let finalOutput := suppressOutputTapeTrace steps output
  have hzero := outputProbeCounterTape_hasBinaryNat_internal 0
  have hzeroRead : (outputProbeCounterTape 0).read ≠ Γ.start := by
    rw [Tape.read, hzero.2.1]
    exact Tape.cells_ne_start_of_hasBinaryString hzero.2 1 le_rfl
  have hsourceStep := outputProbeTM_step_source_internal tm
    (outputProbeCounterTape 0) finalOutput hzeroRead hnext
  have hsourceMissing := outputProbeSourceResultCfg_missing_internal tm
    selected next (outputProbeCounterTape 0)
      (suppressOutputTapeStep finalOutput) symbol hcursor hdir hwrite hzero
  have hfinalRead : finalOutput.read ≠ Γ.start := by
    rw [Tape.read, hphysicalHead]
    intro hstart
    rw [hphysicalCells] at hstart
    simp [Tape.init] at hstart
  have hfinalStable : suppressOutputTapeStep finalOutput = finalOutput := by
    simpa [suppressOutputTapeStep, outputProbeNormalizeTape] using
      outputProbeNormalizeTape_eq_self_internal hfinalRead
  rw [hsourceMissing, hfinalStable] at hsourceStep
  let missingWork : Fin (n + 1) → Tape := fun i =>
    if h : i.val < n then next.work ⟨i.val, h⟩
    else outputProbeCounterTape 0
  let done := outputProbeMissingDoneCfg tm next.input missingWork finalOutput
  have hsourceStep' :
      (outputProbeTM tm).step
        (outputProbeCfg tm selected (outputProbeCounterTape 0)
          finalOutput) =
        some (outputProbeMissingCfg tm next.input missingWork
          finalOutput) := by
    simpa [missingWork, finalOutput] using hsourceStep
  have hmissingStep := outputProbeTM_step_missing_internal tm next.input
    missingWork finalOutput hfinalRead
  have htail : (outputProbeTM tm).reachesIn 2
      (outputProbeCfg tm selected (outputProbeCounterTape 0) finalOutput)
      done := by
    simpa [done] using TM.reachesIn.step hsourceStep'
      (TM.reachesIn.step hmissingStep .zero)
  have hrun := (outputProbeTM tm).reachesIn_trans hsourceRun htail
  refine ⟨sourceSteps + 2, done, hrun, rfl, ?_, ?_, ?_⟩
  · exact outputProbeMissingDone_hasOutput_internal tm next.input
      missingWork finalOutput hphysicalHead hphysicalCells
  · exact outputProbeMissingDone_head_internal tm next.input missingWork
      finalOutput hphysicalHead
  · intro elapsed cfg helapsed hprefix
    have hbound := outputProbeTM_captureTail_prefix_withinAuxSpace_internal
      tm hsourceRun hsourcePrefix htail helapsed hprefix
    simpa [outputProbeCaptureSpace] using hbound

/-- A successful complete transducer run can be replayed to capture any valid
output index. The proof splits according to whether the source halts on the
selected frontier cell or crossed and finalized it earlier. -/
theorem IsTransducer.outputProbeTM_reachesIn_getElem_internal
    {tm : TM n} (htrans : tm.IsTransducer)
    {input bits : List Bool} {steps : ℕ} {final : Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg input) final)
    (hhalt : tm.halted final) (hout : final.output.HasOutput bits)
    (index : ℕ) (hindex : index < bits.length) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm (.ofCfg (tm.initCfg input))
          (outputProbeCounterTape (index + 1)) (Tape.init [])) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [bits[index]'hindex] := by
  let position := index + 1
  let bit := bits[index]'hindex
  have hcell : final.output.cells position = Γ.ofBool bit := by
    simpa [position, bit] using hout.1 index hindex
  have hblank := htrans.initCfg_output_blankAfterHead_reachesIn hreach
  have hpositionLe : position ≤ final.output.head := by
    by_contra hnot
    have hblankCell := hblank position (by omega)
    rw [hcell] at hblankCell
    exact Γ.ofBool_ne_blank bit hblankCell
  by_cases hfrontier : final.output.head = position
  · have hstepsPositive : 0 < steps := by
      by_contra hnot
      have hzero : steps = 0 := by omega
      subst steps
      cases hreach
      simp [position] at hfrontier
    obtain ⟨replaySteps, hsteps⟩ : ∃ replaySteps, steps = replaySteps + 1 :=
      ⟨steps - 1, by omega⟩
    subst steps
    have htrace := htrans.cursorTraceObserved_initCfg hreach
    rw [hfrontier] at htrace
    have hcursor : (CursorCfg.ofCfg final).output =
        .cell (Γ.ofBool bit) := by
      unfold CursorCfg.ofCfg Tape.outputCursor
      simp [hfrontier, position, Tape.read, hcell]
    exact outputProbeTM_reachesIn_cursorTraceObserved_capture_internal tm
      (outputProbeCounterTape position) (Tape.init []) bit htrace
      (Tape.StartInvariant.init_ofBool input)
      (fun _ => Tape.StartInvariant.init_nil)
      (outputProbeCounterTape_hasBinaryNat_internal position)
      Tape.StartInvariant.init_nil hhalt hcursor
      (suppressOutputTapeTrace_succ_init_head replaySteps)
      (suppressOutputTapeTrace_succ_init_cells replaySteps)
  · have hpositionLt : position < final.output.head := by omega
    obtain ⟨prefixSteps, suffixSteps, selected, next, hprefix, hstep,
        hsuffix, hselectedHead, hnextHead⟩ :=
      exists_output_crossing hreach (by simp [position]) hpositionLt
    have hprefixPositive : 0 < prefixSteps := by
      by_contra hnot
      have hzero : prefixSteps = 0 := by omega
      subst prefixSteps
      cases hprefix
      simp [position] at hselectedHead
    obtain ⟨replaySteps, hprefixSteps⟩ :
        ∃ replaySteps, prefixSteps = replaySteps + 1 :=
      ⟨prefixSteps - 1, by omega⟩
    subst prefixSteps
    have htrace := htrans.cursorTraceObserved_initCfg hprefix
    rw [hselectedHead] at htrace
    have hselectedStart : selected.output.StartInvariant :=
      output_startInvariant_reachesIn hprefix Tape.StartInvariant.init_nil
    have hselectedBlank : selected.output.BlankAfterHead :=
      htrans.initCfg_output_blankAfterHead_reachesIn hprefix
    have hnextCursor : tm.cursorStep (.ofCfg selected) =
        some (.ofCfg next) :=
      htrans.cursorStep_commute hselectedStart hselectedBlank hstep
    have hcursor : (CursorCfg.ofCfg selected).output =
        .cell selected.output.read := by
      unfold CursorCfg.ofCfg Tape.outputCursor
      simp [hselectedHead, position]
    have hdir : tm.cursorOutputDirection (.ofCfg selected) =
        Dir3.right :=
      cursorOutputDirection_eq_right_of_output_head_lt
        hselectedStart hstep (by omega)
    have hstepCell := cursorOutputWrite_step_cell hselectedStart hstep
      (show 0 < selected.output.head by omega)
    have hpast := htrans.output_cells_lt_head_reachesIn hsuffix
      (show position < next.output.head by omega)
    have hwriteToΓ :
        (tm.cursorOutputWrite (.ofCfg selected)).toΓ = Γ.ofBool bit := by
      calc
        (tm.cursorOutputWrite (.ofCfg selected)).toΓ =
            next.output.cells selected.output.head := hstepCell.symm
        _ = next.output.cells position := by rw [hselectedHead]
        _ = final.output.cells position := hpast.symm
        _ = Γ.ofBool bit := hcell
    have hwrite : tm.cursorOutputWrite (.ofCfg selected) =
        if bit then Γw.one else Γw.zero := by
      cases hbit : bit <;>
        cases hsymbol : tm.cursorOutputWrite (.ofCfg selected) <;>
        simp [hbit, hsymbol, Γ.ofBool, Γw.toΓ] at hwriteToΓ ⊢
    exact
      outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_internal
        tm (outputProbeCounterTape position) (Tape.init []) bit
        selected.output.read htrace (Tape.StartInvariant.init_ofBool input)
        (fun _ => Tape.StartInvariant.init_nil)
        (outputProbeCounterTape_hasBinaryNat_internal position)
        Tape.StartInvariant.init_nil hnextCursor hcursor hdir hwrite
        (suppressOutputTapeTrace_succ_init_head replaySteps)
      (suppressOutputTapeTrace_succ_init_cells replaySteps)

/-- Cursor states arising from a concrete source run on one fixed input. -/
private def outputProbeSourceInv (tm : TM n) (input : List Bool)
    (cfg : CursorCfg n tm.Q) : Prop :=
  ∃ steps source,
    tm.reachesIn steps (tm.initCfg input) source ∧
      CursorCfg.ofCfg source = cfg

private theorem outputProbeSourceInv_init_internal (tm : TM n)
    (input : List Bool) :
    outputProbeSourceInv tm input (.ofCfg (tm.initCfg input)) :=
  ⟨0, tm.initCfg input, .zero, rfl⟩

private theorem outputProbeSourceInv_step_internal
    {tm : TM n} (htrans : tm.IsTransducer) (input : List Bool)
    {cfg next : CursorCfg n tm.Q}
    (hinv : outputProbeSourceInv tm input cfg)
    (hcursor : tm.cursorStep cfg = some next) :
    outputProbeSourceInv tm input next := by
  obtain ⟨steps, source, hreach, rfl⟩ := hinv
  cases hstep : tm.step source with
  | none =>
      have hhalt : source.state = tm.qhalt :=
        step_eq_none_iff_halted.mp hstep
      simp [cursorStep, CursorCfg.ofCfg, hhalt] at hcursor
  | some sourceNext =>
      have hstart : source.output.StartInvariant :=
        output_startInvariant_reachesIn hreach Tape.StartInvariant.init_nil
      have hblank : source.output.BlankAfterHead :=
        htrans.initCfg_output_blankAfterHead_reachesIn hreach
      have hcommute := htrans.cursorStep_commute hstart hblank hstep
      have hnext : next = CursorCfg.ofCfg sourceNext :=
        Option.some.inj (hcursor.symm.trans hcommute)
      subst next
      exact ⟨steps + 1, sourceNext, tm.reachesIn_snoc hreach hstep, rfl⟩

private theorem ComputesInSpace.outputProbeSourceInv_space_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (cfg : CursorCfg n tm.Q)
    (hinv : outputProbeSourceInv tm input cfg) :
    (∀ i, (cfg.work i).head ≤ max 1 (space input.length)) ∧
      cfg.input.head ≤ input.length + max 1 (space input.length) + 1 := by
  obtain ⟨steps, source, hreach, rfl⟩ := hinv
  have hsource := hcomp.2.1 input source
    (tm.reaches_of_reachesIn hreach)
  refine ⟨fun i => le_trans (hsource.1 i) (le_max_right _ _), ?_⟩
  dsimp only [CursorCfg.ofCfg]
  exact le_trans hsource.2 (by omega)

/-- Every positive output position query terminates, whether it selects a bit,
a blank cell crossed by the source, or a position beyond the final source
frontier. -/
theorem ComputesInSpace.outputProbeTM_index_halts_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm (.ofCfg (tm.initCfg input))
          (outputProbeCounterTape (index + 1)) (Tape.init [])) done ∧
      (outputProbeTM tm).halted done ∧
      (∃ bit, done.output.HasOutput [bit]) ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm (.ofCfg (tm.initCfg input))
            (outputProbeCounterTape (index + 1)) (Tape.init [])) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  obtain ⟨final, hreach, hhalt, _hout⟩ := hcomp.2.2 input
  obtain ⟨steps, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  let position := index + 1
  have htrace := hcomp.1.cursorTraceObserved_initCfg hreachIn
  by_cases habove : final.output.head < position
  · let remaining := position - final.output.head - 1
    have hvalue : (remaining + 1) + final.output.head = position := by
      dsimp only [remaining]
      omega
    have hcounter : (outputProbeCounterTape position).HasBinaryNat
        ((remaining + 1) + final.output.head) := by
      rw [hvalue]
      exact outputProbeCounterTape_hasBinaryNat_internal position
    obtain ⟨probeSteps, done, hrun, hdone, hout, hhead, hspace⟩ :=
      outputProbeTM_reachesIn_cursorTraceObserved_missing_positive_withinAuxSpace_internal
        (inputLength := input.length) (maxCounter := position) tm
        (outputProbeSourceInv tm input) (max 1 (space input.length))
        (remaining := remaining) (outputProbeCounterTape position)
        (Tape.init []) htrace (outputProbeSourceInv_init_internal tm input)
        (outputProbeSourceInv_step_internal hcomp.1 input)
        (hcomp.outputProbeSourceInv_space_internal input)
        (le_max_left 1 (space input.length))
        (Tape.StartInvariant.init_ofBool input)
        (fun _ => Tape.StartInvariant.init_nil) hcounter
        Tape.StartInvariant.init_nil (by omega) hhalt
        (outputProbeNormalize_suppress_init_head_internal steps)
        (outputProbeNormalize_suppress_init_cells_internal steps)
    exact ⟨probeSteps, done, by simpa [position] using hrun, hdone,
      ⟨false, hout⟩, hhead, by simpa [position] using hspace⟩
  · have hpositionLe : position ≤ final.output.head := by omega
    by_cases hfrontier : final.output.head = position
    · have hstepsPositive : 0 < steps := by
        by_contra hnot
        have hzero : steps = 0 := by omega
        subst steps
        cases hreachIn
        simp [position] at hfrontier
      obtain ⟨replaySteps, hsteps⟩ : ∃ replaySteps, steps = replaySteps + 1 :=
        ⟨steps - 1, by omega⟩
      subst steps
      rw [hfrontier] at htrace
      have hcursor : (CursorCfg.ofCfg final).output =
          .cell final.output.read := by
        unfold CursorCfg.ofCfg Tape.outputCursor
        simp [hfrontier, position]
      have hfinalStart : final.output.StartInvariant :=
        output_startInvariant_reachesIn hreachIn Tape.StartInvariant.init_nil
      have hreadNotStart : final.output.read ≠ Γ.start :=
        hfinalStart.read_ne_start (by simp [hfrontier, position])
      cases hsymbol : final.output.read with
      | start => exact (hreadNotStart hsymbol).elim
      | zero =>
          have hcursorBit : (CursorCfg.ofCfg final).output =
              .cell (Γ.ofBool false) := by
            simpa [hsymbol, Γ.ofBool] using hcursor
          obtain ⟨probeSteps, done, hrun, hdone, hout, _hcounter,
              hhead, hspace⟩ :=
            outputProbeTM_reachesIn_cursorTraceObserved_capture_withinAuxSpace_internal
              (inputLength := input.length) tm
              (outputProbeSourceInv tm input)
              (max 1 (space input.length)) (outputProbeCounterTape position)
              (Tape.init []) false htrace
              (outputProbeSourceInv_init_internal tm input)
              (outputProbeSourceInv_step_internal hcomp.1 input)
              (hcomp.outputProbeSourceInv_space_internal input)
              (le_max_left 1 (space input.length))
              (Tape.StartInvariant.init_ofBool input)
              (fun _ => Tape.StartInvariant.init_nil)
              (by simpa using
                outputProbeCounterTape_hasBinaryNat_internal position)
              Tape.StartInvariant.init_nil hhalt hcursorBit
              (suppressOutputTapeTrace_succ_init_head replaySteps)
              (suppressOutputTapeTrace_succ_init_cells replaySteps)
          exact ⟨probeSteps, done, hrun, hdone, ⟨false, hout⟩, hhead, by
            simpa [position] using hspace⟩
      | one =>
          have hcursorBit : (CursorCfg.ofCfg final).output =
              .cell (Γ.ofBool true) := by
            simpa [hsymbol, Γ.ofBool] using hcursor
          obtain ⟨probeSteps, done, hrun, hdone, hout, _hcounter,
              hhead, hspace⟩ :=
            outputProbeTM_reachesIn_cursorTraceObserved_capture_withinAuxSpace_internal
              (inputLength := input.length) tm
              (outputProbeSourceInv tm input)
              (max 1 (space input.length)) (outputProbeCounterTape position)
              (Tape.init []) true htrace
              (outputProbeSourceInv_init_internal tm input)
              (outputProbeSourceInv_step_internal hcomp.1 input)
              (hcomp.outputProbeSourceInv_space_internal input)
              (le_max_left 1 (space input.length))
              (Tape.StartInvariant.init_ofBool input)
              (fun _ => Tape.StartInvariant.init_nil)
              (by simpa using
                outputProbeCounterTape_hasBinaryNat_internal position)
              Tape.StartInvariant.init_nil hhalt hcursorBit
              (suppressOutputTapeTrace_succ_init_head replaySteps)
              (suppressOutputTapeTrace_succ_init_cells replaySteps)
          exact ⟨probeSteps, done, hrun, hdone, ⟨true, hout⟩, hhead, by
            simpa [position] using hspace⟩
      | blank =>
          have hmissing : (outputProbeCaptureCursor
              (CursorCfg.ofCfg final).output : OutputProbeQ n tm.Q) =
              .missing := by
            rw [hcursor, hsymbol]
            rfl
          obtain ⟨probeSteps, done, hrun, hdone, hout, hhead, hspace⟩ :=
            outputProbeTM_reachesIn_cursorTraceObserved_missing_zero_withinAuxSpace_internal
              (inputLength := input.length) (maxCounter := position) tm
              (outputProbeSourceInv tm input)
              (max 1 (space input.length))
              (outputProbeCounterTape position) (Tape.init []) htrace
              (outputProbeSourceInv_init_internal tm input)
              (outputProbeSourceInv_step_internal hcomp.1 input)
              (hcomp.outputProbeSourceInv_space_internal input)
              (le_max_left 1 (space input.length))
              (Tape.StartInvariant.init_ofBool input)
              (fun _ => Tape.StartInvariant.init_nil)
              (by simpa using
                outputProbeCounterTape_hasBinaryNat_internal position)
              Tape.StartInvariant.init_nil (by omega) hhalt hmissing
              (outputProbeNormalize_suppress_init_head_internal
                (replaySteps + 1))
              (outputProbeNormalize_suppress_init_cells_internal
                (replaySteps + 1))
          exact ⟨probeSteps, done, by simpa [position] using hrun, hdone,
            ⟨false, hout⟩, hhead, by simpa [position] using hspace⟩
    · have hpositionLt : position < final.output.head := by omega
      obtain ⟨prefixSteps, suffixSteps, selected, next, hprefix, hstep,
          hsuffix, hselectedHead, hnextHead⟩ :=
        exists_output_crossing hreachIn (by simp [position]) hpositionLt
      have hprefixPositive : 0 < prefixSteps := by
        by_contra hnot
        have hzero : prefixSteps = 0 := by omega
        subst prefixSteps
        cases hprefix
        simp [position] at hselectedHead
      obtain ⟨replaySteps, hprefixSteps⟩ :
          ∃ replaySteps, prefixSteps = replaySteps + 1 :=
        ⟨prefixSteps - 1, by omega⟩
      subst prefixSteps
      have hprefixTrace := hcomp.1.cursorTraceObserved_initCfg hprefix
      rw [hselectedHead] at hprefixTrace
      have hselectedStart : selected.output.StartInvariant :=
        output_startInvariant_reachesIn hprefix Tape.StartInvariant.init_nil
      have hselectedBlank : selected.output.BlankAfterHead :=
        hcomp.1.initCfg_output_blankAfterHead_reachesIn hprefix
      have hnextCursor : tm.cursorStep (.ofCfg selected) =
          some (.ofCfg next) :=
        hcomp.1.cursorStep_commute hselectedStart hselectedBlank hstep
      have hcursor : (CursorCfg.ofCfg selected).output =
          .cell selected.output.read := by
        unfold CursorCfg.ofCfg Tape.outputCursor
        simp [hselectedHead, position]
      have hdir : tm.cursorOutputDirection (.ofCfg selected) =
          Dir3.right :=
        cursorOutputDirection_eq_right_of_output_head_lt
          hselectedStart hstep (by omega)
      cases hwrite : tm.cursorOutputWrite (.ofCfg selected) with
      | zero =>
          obtain ⟨probeSteps, done, hrun, hdone, hout, _hcounter,
              hhead, hspace⟩ :=
            outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_withinAuxSpace_internal
              (inputLength := input.length) tm
              (outputProbeSourceInv tm input)
              (max 1 (space input.length))
              (outputProbeCounterTape position) (Tape.init []) false
              selected.output.read hprefixTrace
              (outputProbeSourceInv_init_internal tm input)
              (outputProbeSourceInv_step_internal hcomp.1 input)
              (hcomp.outputProbeSourceInv_space_internal input)
              (le_max_left 1 (space input.length))
              (Tape.StartInvariant.init_ofBool input)
              (fun _ => Tape.StartInvariant.init_nil)
              (by simpa using
                outputProbeCounterTape_hasBinaryNat_internal position)
              Tape.StartInvariant.init_nil hnextCursor hcursor hdir
              (by simpa using hwrite)
              (suppressOutputTapeTrace_succ_init_head replaySteps)
              (suppressOutputTapeTrace_succ_init_cells replaySteps)
          exact ⟨probeSteps, done, hrun, hdone, ⟨false, hout⟩, hhead, by
            simpa [position] using hspace⟩
      | one =>
          obtain ⟨probeSteps, done, hrun, hdone, hout, _hcounter,
              hhead, hspace⟩ :=
            outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_withinAuxSpace_internal
              (inputLength := input.length) tm
              (outputProbeSourceInv tm input)
              (max 1 (space input.length))
              (outputProbeCounterTape position) (Tape.init []) true
              selected.output.read hprefixTrace
              (outputProbeSourceInv_init_internal tm input)
              (outputProbeSourceInv_step_internal hcomp.1 input)
              (hcomp.outputProbeSourceInv_space_internal input)
              (le_max_left 1 (space input.length))
              (Tape.StartInvariant.init_ofBool input)
              (fun _ => Tape.StartInvariant.init_nil)
              (by simpa using
                outputProbeCounterTape_hasBinaryNat_internal position)
              Tape.StartInvariant.init_nil hnextCursor hcursor hdir
              (by simpa using hwrite)
              (suppressOutputTapeTrace_succ_init_head replaySteps)
              (suppressOutputTapeTrace_succ_init_cells replaySteps)
          exact ⟨probeSteps, done, hrun, hdone, ⟨true, hout⟩, hhead, by
            simpa [position] using hspace⟩
      | blank =>
          obtain ⟨probeSteps, done, hrun, hdone, hout, hhead, hspace⟩ :=
            outputProbeTM_reachesIn_cursorTraceObserved_finalize_missing_withinAuxSpace_internal
              (inputLength := input.length) (maxCounter := position) tm
              (outputProbeSourceInv tm input)
              (max 1 (space input.length))
              (outputProbeCounterTape position) (Tape.init [])
              selected.output.read hprefixTrace
              (outputProbeSourceInv_init_internal tm input)
              (outputProbeSourceInv_step_internal hcomp.1 input)
              (hcomp.outputProbeSourceInv_space_internal input)
              (le_max_left 1 (space input.length))
              (Tape.StartInvariant.init_ofBool input)
              (fun _ => Tape.StartInvariant.init_nil)
              (by simpa using
                outputProbeCounterTape_hasBinaryNat_internal position)
              Tape.StartInvariant.init_nil (by omega) hnextCursor hcursor
              hdir hwrite
              (suppressOutputTapeTrace_succ_init_head replaySteps)
              (suppressOutputTapeTrace_succ_init_cells replaySteps)
          exact ⟨probeSteps, done, by simpa [position] using hrun, hdone,
            ⟨false, hout⟩, hhead, by simpa [position] using hspace⟩

/-- Total arbitrary-index queries transfer to the canonical post-sentinel
wrapper with the same Boolean result and all-prefix space bound. -/
theorem
    ComputesInSpace.outputProbeStartedTM_index_halts_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) :
    ∃ probeSteps done,
      (outputProbeStartedTM tm).reachesIn probeSteps
        (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1))) done ∧
      (outputProbeStartedTM tm).halted done ∧
      (∃ bit, done.output.HasOutput [bit]) ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeStartedTM tm).reachesIn elapsed
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1))) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  obtain ⟨probeSteps, done, hreach, hhalt, hbit, hhead, hspace⟩ :=
    hcomp.outputProbeTM_index_halts_withinAuxSpace_internal input index
  have hprobeNe :
      (outputProbeTM tm).qstart ≠ (outputProbeTM tm).qhalt := by
    intro h
    cases h
  have hstepsNe : probeSteps ≠ 0 := by
    intro hzero
    subst probeSteps
    cases hreach
    exact hprobeNe hhalt
  obtain ⟨tailSteps, hsteps⟩ := Nat.exists_eq_succ_of_ne_zero hstepsNe
  subst probeSteps
  cases hreach with
  | step hstep hrest =>
      rename_i intermediate
      have hmid : intermediate = outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1)) := by
        apply Option.some.inj
        rw [← hstep]
        exact hcomp.1.outputProbeTM_step_startedCfg_total_internal input
          (index + 1)
      subst intermediate
      refine ⟨tailSteps, done,
        (outputProbeTM tm).startedTM_reachesIn_of_source hrest,
        hhalt, hbit, hhead, ?_⟩
      intro elapsed cfg helapsed hstarted
      have hsource := (outputProbeTM tm).source_reachesIn_of_startedTM
        hstarted
      apply hspace (elapsed + 1) cfg
      · omega
      · exact TM.reachesIn.step hstep hsource

/-- A valid output-bit query from a space-bounded transducer carries an
all-prefix auxiliary-space certificate through the final capture seam. -/
theorem ComputesInSpace.outputProbeTM_getElem_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm (.ofCfg (tm.initCfg input))
          (outputProbeCounterTape (index + 1)) (Tape.init [])) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [(f input)[index]'hindex] ∧
      done.work (Fin.last n) = outputProbeCounterTape 0 ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm (.ofCfg (tm.initCfg input))
            (outputProbeCounterTape (index + 1)) (Tape.init [])) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  obtain ⟨final, hreach, hhalt, hout⟩ := hcomp.2.2 input
  obtain ⟨steps, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  let position := index + 1
  let bit := (f input)[index]'hindex
  have hcell : final.output.cells position = Γ.ofBool bit := by
    simpa [position, bit] using hout.1 index hindex
  have hblank := hcomp.1.initCfg_output_blankAfterHead_reachesIn hreachIn
  have hpositionLe : position ≤ final.output.head := by
    by_contra hnot
    have hblankCell := hblank position (by omega)
    rw [hcell] at hblankCell
    exact Γ.ofBool_ne_blank bit hblankCell
  by_cases hfrontier : final.output.head = position
  · have hstepsPositive : 0 < steps := by
      by_contra hnot
      have hzero : steps = 0 := by omega
      subst steps
      cases hreachIn
      simp [position] at hfrontier
    obtain ⟨replaySteps, hsteps⟩ : ∃ replaySteps, steps = replaySteps + 1 :=
      ⟨steps - 1, by omega⟩
    subst steps
    have htrace := hcomp.1.cursorTraceObserved_initCfg hreachIn
    rw [hfrontier] at htrace
    have hcursor : (CursorCfg.ofCfg final).output =
        .cell (Γ.ofBool bit) := by
      unfold CursorCfg.ofCfg Tape.outputCursor
      simp [hfrontier, position, Tape.read, hcell]
    simpa [position, bit] using
      (outputProbeTM_reachesIn_cursorTraceObserved_capture_withinAuxSpace_internal
        (inputLength := input.length) tm (outputProbeSourceInv tm input)
        (max 1 (space input.length))
        (outputProbeCounterTape position) (Tape.init []) bit htrace
        (outputProbeSourceInv_init_internal tm input)
        (outputProbeSourceInv_step_internal hcomp.1 input)
        (hcomp.outputProbeSourceInv_space_internal input)
        (le_max_left 1 (space input.length))
        (Tape.StartInvariant.init_ofBool input)
        (fun _ => Tape.StartInvariant.init_nil)
        (outputProbeCounterTape_hasBinaryNat_internal position)
        Tape.StartInvariant.init_nil hhalt hcursor
        (suppressOutputTapeTrace_succ_init_head replaySteps)
        (suppressOutputTapeTrace_succ_init_cells replaySteps))
  · have hpositionLt : position < final.output.head := by omega
    obtain ⟨prefixSteps, suffixSteps, selected, next, hprefix, hstep,
        hsuffix, hselectedHead, hnextHead⟩ :=
      exists_output_crossing hreachIn (by simp [position]) hpositionLt
    have hprefixPositive : 0 < prefixSteps := by
      by_contra hnot
      have hzero : prefixSteps = 0 := by omega
      subst prefixSteps
      cases hprefix
      simp [position] at hselectedHead
    obtain ⟨replaySteps, hprefixSteps⟩ :
        ∃ replaySteps, prefixSteps = replaySteps + 1 :=
      ⟨prefixSteps - 1, by omega⟩
    subst prefixSteps
    have htrace := hcomp.1.cursorTraceObserved_initCfg hprefix
    rw [hselectedHead] at htrace
    have hselectedStart : selected.output.StartInvariant :=
      output_startInvariant_reachesIn hprefix Tape.StartInvariant.init_nil
    have hselectedBlank : selected.output.BlankAfterHead :=
      hcomp.1.initCfg_output_blankAfterHead_reachesIn hprefix
    have hnextCursor : tm.cursorStep (.ofCfg selected) =
        some (.ofCfg next) :=
      hcomp.1.cursorStep_commute hselectedStart hselectedBlank hstep
    have hcursor : (CursorCfg.ofCfg selected).output =
        .cell selected.output.read := by
      unfold CursorCfg.ofCfg Tape.outputCursor
      simp [hselectedHead, position]
    have hdir : tm.cursorOutputDirection (.ofCfg selected) = Dir3.right :=
      cursorOutputDirection_eq_right_of_output_head_lt
        hselectedStart hstep (by omega)
    have hstepCell := cursorOutputWrite_step_cell hselectedStart hstep
      (show 0 < selected.output.head by omega)
    have hpast := hcomp.1.output_cells_lt_head_reachesIn hsuffix
      (show position < next.output.head by omega)
    have hwriteToΓ :
        (tm.cursorOutputWrite (.ofCfg selected)).toΓ = Γ.ofBool bit := by
      calc
        (tm.cursorOutputWrite (.ofCfg selected)).toΓ =
            next.output.cells selected.output.head := hstepCell.symm
        _ = next.output.cells position := by rw [hselectedHead]
        _ = final.output.cells position := hpast.symm
        _ = Γ.ofBool bit := hcell
    have hwrite : tm.cursorOutputWrite (.ofCfg selected) =
        if bit then Γw.one else Γw.zero := by
      cases hbit : bit <;>
        cases hsymbol : tm.cursorOutputWrite (.ofCfg selected) <;>
        simp [hbit, hsymbol, Γ.ofBool, Γw.toΓ] at hwriteToΓ ⊢
    simpa [position, bit] using
      (outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_withinAuxSpace_internal
        (inputLength := input.length) tm (outputProbeSourceInv tm input)
        (max 1 (space input.length))
        (outputProbeCounterTape position) (Tape.init []) bit
        selected.output.read htrace
        (outputProbeSourceInv_init_internal tm input)
        (outputProbeSourceInv_step_internal hcomp.1 input)
        (hcomp.outputProbeSourceInv_space_internal input)
        (le_max_left 1 (space input.length))
        (Tape.StartInvariant.init_ofBool input)
        (fun _ => Tape.StartInvariant.init_nil)
        (outputProbeCounterTape_hasBinaryNat_internal position)
        Tape.StartInvariant.init_nil hnextCursor hcursor hdir hwrite
        (suppressOutputTapeTrace_succ_init_head replaySteps)
        (suppressOutputTapeTrace_succ_init_cells replaySteps))

/-- A space-bounded function transducer's probe captures every valid output
index from the canonical source input and binary position tape. -/
theorem ComputesInSpace.outputProbeTM_getElem_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm (.ofCfg (tm.initCfg input))
          (outputProbeCounterTape (index + 1)) (Tape.init [])) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [(f input)[index]'hindex] := by
  obtain ⟨probeSteps, done, hreach, hhalt, hout, _hcounter, _hhead,
      _hspace⟩ :=
    hcomp.outputProbeTM_getElem_withinAuxSpace_internal input index hindex
  exact ⟨probeSteps, done, hreach, hhalt, hout⟩

private theorem qstart_ne_qhalt_of_computesInSpace_getElem_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    tm.qstart ≠ tm.qhalt := by
  intro hstart
  obtain ⟨final, hreach, _hhalt, hout⟩ := hcomp.2.2 input
  obtain ⟨steps, hreachIn⟩ := tm.reaches_to_reachesIn hreach
  have hinitHalt : tm.halted (tm.initCfg input) := by
    simpa [TM.halted, Cfg.isHalted, Cfg.init] using hstart
  have hsteps : steps = 0 := by
    have hle := tm.reachesIn_le_halt hreachIn
      (TM.reachesIn.zero :
        tm.reachesIn 0 (tm.initCfg input) (tm.initCfg input)) hinitHalt
    omega
  subst steps
  cases hreachIn
  have hcell := hout.1 index hindex
  cases hbit : (f input)[index] <;>
    simp [Tape.init, Γ.ofBool, hbit] at hcell

/-- A valid output-bit query from the canonical post-sentinel frame preserves
the complete all-prefix auxiliary-space certificate. -/
theorem ComputesInSpace.outputProbeStartedTM_getElem_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      (outputProbeStartedTM tm).reachesIn probeSteps
        (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1))) done ∧
      (outputProbeStartedTM tm).halted done ∧
      done.output.HasOutput [(f input)[index]'hindex] ∧
      done.work (Fin.last n) = outputProbeCounterTape 0 ∧
      done.output.head = 2 ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeStartedTM tm).reachesIn elapsed
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1))) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  have hne := qstart_ne_qhalt_of_computesInSpace_getElem_internal
    hcomp input index hindex
  obtain ⟨probeSteps, done, hreach, hhalt, hout, hcounter, hhead,
      hspace⟩ :=
    hcomp.outputProbeTM_getElem_withinAuxSpace_internal input index hindex
  have hprobeNe :
      (outputProbeTM tm).qstart ≠ (outputProbeTM tm).qhalt := by
    intro h
    cases h
  have hstepsNe : probeSteps ≠ 0 := by
    intro hzero
    subst probeSteps
    cases hreach
    exact hprobeNe hhalt
  obtain ⟨tailSteps, hsteps⟩ := Nat.exists_eq_succ_of_ne_zero hstepsNe
  subst probeSteps
  cases hreach with
  | step hstep hrest =>
      rename_i intermediate
      have hmid : intermediate = outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1)) := by
        apply Option.some.inj
        rw [← hstep]
        exact hcomp.1.outputProbeTM_step_startedCfg_internal input
          (index + 1) hne
      subst intermediate
      refine ⟨tailSteps, done,
        (outputProbeTM tm).startedTM_reachesIn_of_source hrest,
        hhalt, hout, hcounter, hhead, ?_⟩
      intro elapsed cfg helapsed hstarted
      have hsource := (outputProbeTM tm).source_reachesIn_of_startedTM
        hstarted
      apply hspace (elapsed + 1) cfg
      · omega
      · exact TM.reachesIn.step hstep hsource

/-- A space-bounded transducer's valid output bit can be queried from the
canonical post-sentinel probe frame. -/
theorem ComputesInSpace.outputProbeStartedTM_getElem_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      (outputProbeStartedTM tm).reachesIn probeSteps
        (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1))) done ∧
      (outputProbeStartedTM tm).halted done ∧
      done.output.HasOutput [(f input)[index]'hindex] := by
  obtain ⟨probeSteps, done, hreach, hhalt, hout, _hcounter, _hhead,
      _hspace⟩ :=
    hcomp.outputProbeStartedTM_getElem_withinAuxSpace_internal
      input index hindex
  exact ⟨probeSteps, done, hreach, hhalt, hout⟩

/-- Total restartable queries can be retargeted into a fresh work tape while
retaining their Boolean result, blank-support envelope, and all-prefix space
bound. -/
theorem
    ComputesInSpace.outputProbeStartedRetargetTM_index_halts_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) :
    ∃ probeSteps done,
      ((outputProbeStartedTM tm).retargetOutput).reachesIn probeSteps
        ((outputProbeStartedTM tm).retargetCfg
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1)))) done ∧
      ((outputProbeStartedTM tm).retargetOutput).halted done ∧
      (∃ bit, (done.work (Fin.last (n + 1))).HasOutput [bit]) ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      done.output = (Tape.init []).move Dir3.right ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        ((outputProbeStartedTM tm).retargetOutput).reachesIn elapsed
          ((outputProbeStartedTM tm).retargetCfg
            (outputProbeStartedCfg tm input
              (outputProbeCounterTape (index + 1)))) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  obtain ⟨probeSteps, sourceDone, hsourceRun, hhalt, hbit, hhead,
      hsourcePrefix⟩ :=
    hcomp.outputProbeStartedTM_index_halts_withinAuxSpace_internal
      input index
  let sourceTM := outputProbeStartedTM tm
  let budget := outputProbeCaptureSpace (max 1 (space input.length))
    (index + 1)
  have hsourceTrans : sourceTM.IsTransducer :=
    (outputProbeTM_isTransducer_internal tm).startedTM_internal
  have hretargetRun :=
    retargetOutput_reachesIn_retargetCfg_frame sourceTM hsourceRun
  have hretargetPrefix : ∀ elapsed cfg, elapsed ≤ probeSteps →
      sourceTM.retargetOutput.reachesIn elapsed
        (sourceTM.retargetCfg (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1)))) cfg →
      cfg.WithinAuxSpace input.length budget := by
    intro elapsed cfg helapsed hretarget
    let remaining := probeSteps - elapsed
    have htime : elapsed + remaining = probeSteps := by
      dsimp only [remaining]
      omega
    rw [← htime] at hsourceRun
    obtain ⟨sourceMid, hsourceMid, hsourceRest⟩ :=
      reachesIn_split_internal hsourceRun
    have hretargetMid :=
      retargetOutput_reachesIn_retargetCfg_frame sourceTM hsourceMid
    have hcfg : cfg = sourceTM.retargetCfg sourceMid :=
      (sourceTM.retargetOutput).reachesIn_right_unique hretarget hretargetMid
    subst cfg
    have hmidSpace : sourceMid.WithinAuxSpace input.length budget := by
      simpa [budget] using
        hsourcePrefix elapsed sourceMid helapsed hsourceMid
    have hmidOutput : sourceMid.output.head ≤ 2 := by
      have hmono := hsourceTrans.output_head_mono_reachesIn hsourceRest
      omega
    constructor
    · intro i
      by_cases hi : i.val < n + 1
      · rw [retargetCfg_work_lt sourceTM sourceMid i hi]
        exact hmidSpace.1 ⟨i.val, hi⟩
      · have hilast : i = Fin.last (n + 1) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst i
        rw [retargetCfg_work_last]
        apply le_trans hmidOutput
        dsimp only [budget, outputProbeCaptureSpace,
          outputProbeReplaySpace, outputProbePositiveSpace, binaryPredSpace]
        omega
    · simpa only [retargetCfg_input] using hmidSpace.2
  have hblankParked : ((Tape.init []).move Dir3.right).BlankAfter budget := by
    simpa only [Tape.BlankAfter, Tape.move_cells] using
      Tape.BlankAfter.init_nil budget
  have hstartBlank : ∀ i,
      ((sourceTM.retargetCfg (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1)))).work i).BlankAfter budget := by
    intro i
    by_cases hi : i.val < n + 1
    · rw [retargetCfg_work_lt sourceTM _ i hi]
      by_cases hsource : i.val < n
      · simpa [outputProbeStartedCfg, hsource] using hblankParked
      · have hilast : (⟨i.val, hi⟩ : Fin (n + 1)) = Fin.last n := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [hilast]
        have hcounterBlank :
            (outputProbeCounterTape (index + 1)).BlankAfter budget := by
          have hcontent : (outputProbeCounterTape
              (index + 1)).HasBinaryContent (index + 1).bits :=
            (outputProbeCounterTape_hasBinaryNat_internal (index + 1)).2.2
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
      rw [retargetCfg_work_last]
      simpa [outputProbeStartedCfg] using hblankParked
  refine ⟨probeSteps, sourceTM.retargetCfg sourceDone, hretargetRun,
    hhalt, ?_, ?_, rfl, hretargetPrefix⟩
  · obtain ⟨bit, hout⟩ := hbit
    exact ⟨bit, by rw [retargetCfg_work_last]; exact hout⟩
  · intro i
    exact work_blankAfter_reachesIn i (hstartBlank i) hretargetRun
      hretargetPrefix

/-- Redirecting the restartable query preserves its all-prefix space bound;
the captured one-bit output has head two and therefore fits inside the same
budget on the fresh final work tape. -/
theorem ComputesInSpace.outputProbeStartedRetargetTM_getElem_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      ((outputProbeStartedTM tm).retargetOutput).reachesIn probeSteps
        ((outputProbeStartedTM tm).retargetCfg
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1)))) done ∧
      ((outputProbeStartedTM tm).retargetOutput).halted done ∧
      (done.work (Fin.last (n + 1))).HasOutput
        [(f input)[index]'hindex] ∧
      done.work ⟨n, by omega⟩ = outputProbeCounterTape 0 ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      done.output = (Tape.init []).move Dir3.right ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        ((outputProbeStartedTM tm).retargetOutput).reachesIn elapsed
          ((outputProbeStartedTM tm).retargetCfg
            (outputProbeStartedCfg tm input
              (outputProbeCounterTape (index + 1)))) cfg →
        cfg.WithinAuxSpace input.length
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1)) := by
  obtain ⟨probeSteps, sourceDone, hsourceRun, hhalt, hout, hcounter,
      hhead, hsourcePrefix⟩ :=
    hcomp.outputProbeStartedTM_getElem_withinAuxSpace_internal
      input index hindex
  let sourceTM := outputProbeStartedTM tm
  let budget := outputProbeCaptureSpace (max 1 (space input.length))
    (index + 1)
  have hsourceTrans : sourceTM.IsTransducer :=
    (outputProbeTM_isTransducer_internal tm).startedTM_internal
  have hretargetRun :=
    retargetOutput_reachesIn_retargetCfg_frame sourceTM hsourceRun
  have hretargetPrefix : ∀ elapsed cfg, elapsed ≤ probeSteps →
      sourceTM.retargetOutput.reachesIn elapsed
        (sourceTM.retargetCfg (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1)))) cfg →
      cfg.WithinAuxSpace input.length budget := by
    intro elapsed cfg helapsed hretarget
    let remaining := probeSteps - elapsed
    have htime : elapsed + remaining = probeSteps := by
      dsimp only [remaining]
      omega
    rw [← htime] at hsourceRun
    obtain ⟨sourceMid, hsourceMid, hsourceRest⟩ :=
      reachesIn_split_internal hsourceRun
    have hretargetMid :=
      retargetOutput_reachesIn_retargetCfg_frame sourceTM hsourceMid
    have hcfg : cfg = sourceTM.retargetCfg sourceMid :=
      (sourceTM.retargetOutput).reachesIn_right_unique hretarget hretargetMid
    subst cfg
    have hmidSpace : sourceMid.WithinAuxSpace input.length budget := by
      simpa [budget] using
        hsourcePrefix elapsed sourceMid helapsed hsourceMid
    have hmidOutput : sourceMid.output.head ≤ 2 := by
      have hmono := hsourceTrans.output_head_mono_reachesIn hsourceRest
      omega
    constructor
    · intro i
      by_cases hi : i.val < n + 1
      · rw [retargetCfg_work_lt sourceTM sourceMid i hi]
        exact hmidSpace.1 ⟨i.val, hi⟩
      · have hilast : i = Fin.last (n + 1) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst i
        rw [retargetCfg_work_last]
        apply le_trans hmidOutput
        dsimp only [budget, outputProbeCaptureSpace,
          outputProbeReplaySpace, outputProbePositiveSpace, binaryPredSpace]
        omega
    · simpa only [retargetCfg_input] using hmidSpace.2
  have hblankParked : ((Tape.init []).move Dir3.right).BlankAfter budget := by
    simpa only [Tape.BlankAfter, Tape.move_cells] using
      Tape.BlankAfter.init_nil budget
  have hstartBlank : ∀ i,
      ((sourceTM.retargetCfg (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1)))).work i).BlankAfter budget := by
    intro i
    by_cases hi : i.val < n + 1
    · rw [retargetCfg_work_lt sourceTM _ i hi]
      by_cases hsource : i.val < n
      · simpa [outputProbeStartedCfg, hsource] using hblankParked
      · have hilast : (⟨i.val, hi⟩ : Fin (n + 1)) = Fin.last n := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [hilast]
        have hcounterBlank :
            (outputProbeCounterTape (index + 1)).BlankAfter budget := by
          have hcontent : (outputProbeCounterTape
              (index + 1)).HasBinaryContent (index + 1).bits :=
            (outputProbeCounterTape_hasBinaryNat_internal (index + 1)).2.2
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
      rw [retargetCfg_work_last]
      simpa [outputProbeStartedCfg] using hblankParked
  refine ⟨probeSteps, sourceTM.retargetCfg sourceDone, hretargetRun,
    hhalt, ?_, ?_, ?_, rfl, hretargetPrefix⟩
  · rw [retargetCfg_work_last]
    exact hout
  · rw [retargetCfg_work_lt]
    exact hcounter
  · intro i
    exact work_blankAfter_reachesIn i (hstartBlank i) hretargetRun
      hretargetPrefix

/-- Redirect the restartable probe's captured output bit to a fresh work tape,
leaving the enclosing machine's real output parked and blank. -/
theorem ComputesInSpace.outputProbeStartedRetargetTM_getElem_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      ((outputProbeStartedTM tm).retargetOutput).reachesIn probeSteps
        ((outputProbeStartedTM tm).retargetCfg
          (outputProbeStartedCfg tm input
            (outputProbeCounterTape (index + 1)))) done ∧
      ((outputProbeStartedTM tm).retargetOutput).halted done ∧
      (done.work (Fin.last (n + 1))).HasOutput
        [(f input)[index]'hindex] ∧
      done.output = (Tape.init []).move Dir3.right := by
  obtain ⟨probeSteps, done, hreach, hhalt, hout, _hcounter, _hblank,
      houtput, _hspace⟩ :=
    hcomp.outputProbeStartedRetargetTM_getElem_withinAuxSpace_internal
      input index hindex
  exact ⟨probeSteps, done, hreach, hhalt, hout, houtput⟩

/-- A total retargeted query can run inside an arbitrary stable controller
frame, preserving one Boolean result and the complete cleanup support bound. -/
theorem
    ComputesInSpace.placeOutputProbeStartedRetargetTM_index_halts_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (pre post : ℕ)
    (input : List Bool) (index : ℕ)
    (extras : Fin (pre + (n + 2) + post) → Tape)
    {frameSpace : ℕ}
    (hextra : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let start := (outputProbeStartedTM tm).retargetCfg
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1)))
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
      (placeWorkCfg queryTM pre post extras done).output =
        (Tape.init []).move Dir3.right ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (placeWorkTM pre post queryTM).reachesIn elapsed
          (placeWorkCfg queryTM pre post extras start) cfg →
        cfg.WithinAuxSpace input.length
          (max
            (outputProbeCaptureSpace (max 1 (space input.length))
              (index + 1))
            frameSpace) := by
  dsimp only
  obtain ⟨probeSteps, done, hreach, hhalt, hbit, hblank, houtput,
      hprefix⟩ :=
    hcomp.outputProbeStartedRetargetTM_index_halts_withinAuxSpace_internal
      input index
  obtain ⟨hplaced, hplacedPrefix⟩ :=
    placeWorkTM_reachesIn_placeWorkCfg_stable_withinAuxSpace_internal
      ((outputProbeStartedTM tm).retargetOutput) pre post extras hreach
      hextra hprefix hframe
  refine ⟨probeSteps, done, hplaced, hhalt, ?_, ?_, ?_, hplacedPrefix⟩
  · obtain ⟨bit, hout⟩ := hbit
    refine ⟨bit, ?_⟩
    rw [placeWorkCfg_work_middle]
    exact hout
  · intro i
    rw [placeWorkCfg_work_middle]
    exact hblank i
  · simpa only [placeWorkCfg_output] using houtput

/-- A restartable retargeted output query can run inside an arbitrary stable
controller frame. The exact source endpoint is embedded back into that frame,
the captured bit is exposed at its physical placed tape, and every prefix uses
at most the maximum of the query and frame budgets. -/
theorem ComputesInSpace.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (pre post : ℕ)
    (input : List Bool) (index : ℕ) (hindex : index < (f input).length)
    (extras : Fin (pre + (n + 2) + post) → Tape)
    {frameSpace : ℕ}
    (hextra : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle pre (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let start := (outputProbeStartedTM tm).retargetCfg
      (outputProbeStartedCfg tm input
        (outputProbeCounterTape (index + 1)))
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
      (placeWorkCfg queryTM pre post extras done).output =
        (Tape.init []).move Dir3.right ∧
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
      houtput, hprefix⟩ :=
    hcomp.outputProbeStartedRetargetTM_getElem_withinAuxSpace_internal
      input index hindex
  obtain ⟨hplaced, hplacedPrefix⟩ :=
    placeWorkTM_reachesIn_placeWorkCfg_stable_withinAuxSpace_internal
      ((outputProbeStartedTM tm).retargetOutput) pre post extras hreach
      hextra hprefix hframe
  refine ⟨probeSteps, done, hplaced, ?_, ?_, ?_, ?_, ?_, hplacedPrefix⟩
  · exact hhalt
  · rw [placeWorkCfg_work_middle]
    exact hout
  · rw [placeWorkCfg_work_middle]
    exact hcounter
  · intro i
    rw [placeWorkCfg_work_middle]
    exact hblank i
  · simpa only [placeWorkCfg_output] using houtput

end TM

end Complexity
