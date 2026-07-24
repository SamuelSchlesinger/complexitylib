/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputCursor.Defs

/-!
# Finite cursors for append-only output tapes -- proof internals
-/

namespace Complexity

namespace TM.OutputCursor

theorem read_outputCursor_internal {tape : Tape}
    (hstart : tape.StartInvariant) :
    tape.outputCursor.read = tape.read := by
  unfold Tape.outputCursor
  split
  · next hhead =>
    simp only [read, Tape.read, hhead]
    exact hstart.1.symm
  · rfl

@[simp] theorem next_start_right_internal (write : Γw) :
    OutputCursor.next .start write .right = .cell Γ.blank := rfl

@[simp] theorem next_cell_right_internal (symbol : Γ) (write : Γw) :
    OutputCursor.next (.cell symbol) write .right = .cell Γ.blank := rfl

@[simp] theorem next_cell_stay_internal (symbol : Γ) (write : Γw) :
    OutputCursor.next (.cell symbol) write .stay = .cell write.toΓ := rfl

end TM.OutputCursor

namespace Tape

theorem outputCursor_writeAndMove_internal {tape : Tape}
    (hblank : tape.BlankAfterHead) (write : Γw) (direction : Dir3)
    (hnoleft : direction ≠ Dir3.left) :
    (tape.writeAndMove write.toΓ direction).outputCursor =
      tape.outputCursor.next write direction := by
  cases direction with
  | left => exact (hnoleft rfl).elim
  | right =>
      unfold outputCursor TM.OutputCursor.next
      by_cases hhead : tape.head = 0
      · have hnext : tape.cells (tape.head + 1) = Γ.blank :=
          hblank _ (by omega)
        have hcell : tape.cells 1 = Γ.blank := by
          simpa only [hhead, zero_add] using hnext
        simp [Tape.writeAndMove, Tape.move, Tape.write, Tape.read, hhead,
          hcell]
      · have hnext : tape.cells (tape.head + 1) = Γ.blank :=
          hblank _ (by omega)
        simp [Tape.writeAndMove, Tape.move, Tape.write, Tape.read, hhead,
          hnext]
  | stay =>
      unfold outputCursor TM.OutputCursor.next
      by_cases hhead : tape.head = 0
      · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
      · simp [Tape.writeAndMove, Tape.move, Tape.write, Tape.read, hhead]

end Tape

namespace TM

theorem output_startInvariant_step_internal {tm : TM n}
    {cfg cfg' : Cfg n tm.Q} (hstart : cfg.output.StartInvariant)
    (hstep : tm.step cfg = some cfg') :
    cfg'.output.StartInvariant := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    exact hstart.writeAndMove _ _

theorem output_startInvariant_reachesIn_internal {tm : TM n}
    {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant) :
    cfg'.output.StartInvariant := by
  induction hreach with
  | zero => exact hstart
  | step hstep _ ih =>
      exact ih (output_startInvariant_step_internal hstart hstep)

theorem IsTransducer.cursorStep_commute_internal {tm : TM n}
    (htrans : tm.IsTransducer) {cfg cfg' : Cfg n tm.Q}
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead)
    (hstep : tm.step cfg = some cfg') :
    tm.cursorStep (.ofCfg cfg) = some (.ofCfg cfg') := by
  have hread : cfg.output.outputCursor.read = cfg.output.read :=
    OutputCursor.read_outputCursor_internal hstart
  generalize htransition :
    tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read = transition
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
    outputDir⟩ := transition
  have hnoleft : outputDir ≠ Dir3.left := by
    have := htrans cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read
    rw [htransition] at this
    exact this
  simp only [TM.step, htransition] at hstep
  by_cases hhalt : cfg.state = tm.qhalt
  · simp [hhalt] at hstep
  · simp only [hhalt, if_false, Option.some.injEq] at hstep
    subst cfg'
    unfold cursorStep CursorCfg.ofCfg
    rw [hread, htransition]
    simp only [hhalt, if_false, Option.some.injEq, CursorCfg.mk.injEq,
      true_and]
    exact (Tape.outputCursor_writeAndMove_internal hblank outputWrite
      outputDir hnoleft).symm

private theorem writeAndMove_head_eq_add_advanceCount
    (tape : Tape) (write : Γw) (direction : Dir3)
    (hnoleft : direction ≠ Dir3.left) :
    (tape.writeAndMove write direction).head =
      tape.head + OutputCursor.advanceCount direction := by
  cases direction with
  | left => exact (hnoleft rfl).elim
  | right =>
      simp [Tape.writeAndMove, Tape.move, Tape.write_head,
        OutputCursor.advanceCount]
  | stay =>
      simp [Tape.writeAndMove, Tape.move, Tape.write_head,
        OutputCursor.advanceCount]

theorem IsTransducer.cursorStepObserved_commute_internal {tm : TM n}
    (htrans : tm.IsTransducer) {cfg cfg' : Cfg n tm.Q}
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead)
    (hstep : tm.step cfg = some cfg') :
    tm.cursorStepObserved (.ofCfg cfg) =
      some (.ofCfg cfg', tm.cursorOutputEvent (.ofCfg cfg)) := by
  rw [cursorStepObserved,
    htrans.cursorStep_commute_internal hstart hblank hstep]
  rfl

theorem IsTransducer.cursorStepObserved_head_internal {tm : TM n}
    (htrans : tm.IsTransducer) {cfg cfg' : Cfg n tm.Q}
    (hstart : cfg.output.StartInvariant)
    (hstep : tm.step cfg = some cfg') :
    cfg'.output.head = cfg.output.head +
      (tm.cursorOutputEvent (.ofCfg cfg)).advance := by
  have hread : cfg.output.outputCursor.read = cfg.output.read :=
    OutputCursor.read_outputCursor_internal hstart
  generalize htransition :
    tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read = transition
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
    outputDir⟩ := transition
  have hnoleft : outputDir ≠ Dir3.left := by
    have := htrans cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read
    rw [htransition] at this
    exact this
  have hdir : tm.cursorOutputDirection (.ofCfg cfg) = outputDir := by
    unfold cursorOutputDirection CursorCfg.ofCfg
    rw [hread, htransition]
  simp only [TM.step, htransition] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    subst cfg'
    simp only [cursorOutputEvent, hdir]
    exact writeAndMove_head_eq_add_advanceCount cfg.output outputWrite
      outputDir hnoleft

theorem IsTransducer.output_head_mono_step_internal {tm : TM n}
    (htrans : tm.IsTransducer) {cfg cfg' : Cfg n tm.Q}
    (hstep : tm.step cfg = some cfg') :
    cfg.output.head ≤ cfg'.output.head := by
  generalize htransition :
    tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read = transition
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
    outputDir⟩ := transition
  have hnoleft : outputDir ≠ Dir3.left := by
    have := htrans cfg.state cfg.input.read
      (fun i => (cfg.work i).read) cfg.output.read
    rw [htransition] at this
    exact this
  simp only [TM.step, htransition] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    subst cfg'
    cases outputDir with
    | left => exact (hnoleft rfl).elim
    | right => simp [Tape.writeAndMove, Tape.move, Tape.write_head]
    | stay => simp [Tape.writeAndMove, Tape.move, Tape.write_head]

private theorem output_head_step_le_internal {tm : TM n}
    {cfg cfg' : Cfg n tm.Q} (hstep : tm.step cfg = some cfg') :
    cfg'.output.head ≤ cfg.output.head + 1 := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    generalize hdir :
      (tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
        cfg.output.read).2.2.2.2.2 = direction
    cases direction with
    | left =>
        simp [Tape.writeAndMove, Tape.move, Tape.write_head]
        omega
    | right => simp [Tape.writeAndMove, Tape.move, Tape.write_head]
    | stay => simp [Tape.writeAndMove, Tape.move, Tape.write_head]

theorem IsTransducer.output_head_mono_reachesIn_internal {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg') :
    cfg.output.head ≤ cfg'.output.head := by
  induction hreach with
  | zero => exact le_rfl
  | step hstep _ ih =>
      exact (htrans.output_head_mono_step_internal hstep).trans ih

private theorem output_cells_lt_head_step_internal {tm : TM n}
    {cfg cfg' : Cfg n tm.Q} (hstep : tm.step cfg = some cfg')
    {position : ℕ} (hposition : position < cfg.output.head) :
    cfg'.output.cells position = cfg.output.cells position := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    have hhead : cfg.output.head ≠ 0 := by omega
    have hne : cfg.output.head ≠ position := by omega
    cases (tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read).2.2.2.2.2 <;>
      simp [Tape.writeAndMove, Tape.move, Tape.write, hhead,
        Function.update_of_ne (Ne.symm hne)]

theorem IsTransducer.output_cells_lt_head_reachesIn_internal {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg') {position : ℕ}
    (hposition : position < cfg.output.head) :
    cfg'.output.cells position = cfg.output.cells position := by
  induction hreach with
  | zero => rfl
  | step hstep _ ih =>
      have hmono := htrans.output_head_mono_step_internal hstep
      rw [ih (hposition.trans_le hmono)]
      exact output_cells_lt_head_step_internal hstep hposition

theorem cursorOutputDirection_eq_right_of_output_head_lt_internal
    {tm : TM n} {cfg cfg' : Cfg n tm.Q}
    (hstart : cfg.output.StartInvariant)
    (hstep : tm.step cfg = some cfg')
    (hhead : cfg.output.head < cfg'.output.head) :
    tm.cursorOutputDirection (.ofCfg cfg) = Dir3.right := by
  generalize htransition :
    tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read = transition
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
    outputDir⟩ := transition
  have hdirection :
      tm.cursorOutputDirection (.ofCfg cfg) = outputDir := by
    have hread := OutputCursor.read_outputCursor_internal hstart
    unfold cursorOutputDirection CursorCfg.ofCfg
    rw [hread, htransition]
  simp only [TM.step, htransition] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    subst cfg'
    rw [hdirection]
    cases outputDir with
    | left =>
        simp [Tape.writeAndMove, Tape.move, Tape.write_head] at hhead
        omega
    | right => rfl
    | stay => simp [Tape.writeAndMove, Tape.move, Tape.write_head] at hhead

theorem cursorOutputWrite_step_cell_internal {tm : TM n}
    {cfg cfg' : Cfg n tm.Q} (hstart : cfg.output.StartInvariant)
    (hstep : tm.step cfg = some cfg')
    (hpositive : 0 < cfg.output.head) :
    cfg'.output.cells cfg.output.head =
      (tm.cursorOutputWrite (.ofCfg cfg)).toΓ := by
  generalize htransition :
    tm.δ cfg.state cfg.input.read (fun i => (cfg.work i).read)
      cfg.output.read = transition
  obtain ⟨state, workWrites, outputWrite, inputDir, workDirs,
    outputDir⟩ := transition
  have hwrite : tm.cursorOutputWrite (.ofCfg cfg) = outputWrite := by
    have hread := OutputCursor.read_outputCursor_internal hstart
    unfold cursorOutputWrite CursorCfg.ofCfg
    rw [hread, htransition]
  simp only [TM.step, htransition] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    subst cfg'
    rw [hwrite]
    have hhead : cfg.output.head ≠ 0 := by omega
    cases outputDir <;>
      simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]

theorem exists_output_crossing_internal {tm : TM n}
    {steps position : ℕ}
    {cfg final : Cfg n tm.Q} (hreach : tm.reachesIn steps cfg final)
    (hbefore : cfg.output.head ≤ position)
    (hafter : position < final.output.head) :
    ∃ prefixSteps suffixSteps selected next,
      tm.reachesIn prefixSteps cfg selected ∧
      tm.step selected = some next ∧
      tm.reachesIn suffixSteps next final ∧
      selected.output.head = position ∧
      next.output.head = position + 1 := by
  induction hreach with
  | zero => omega
  | @step source next remaining final hstep hrest ih =>
      by_cases hcrossed : position < next.output.head
      · have hbound := output_head_step_le_internal hstep
        refine ⟨0, remaining, source, next, .zero, hstep, hrest, ?_, ?_⟩
        · omega
        · omega
      · obtain ⟨prefixSteps, suffixSteps, selected, crossed, hprefix, hstep',
          hsuffix, hselected, hcrossed'⟩ :=
          ih (Nat.le_of_not_gt hcrossed) hafter
        exact ⟨prefixSteps + 1, suffixSteps, selected, crossed,
          .step hstep hprefix, hstep', hsuffix, hselected, hcrossed'⟩

theorem IsTransducer.cursorTrace_commute_internal {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) :
    tm.cursorTrace steps (.ofCfg cfg) = some (.ofCfg cfg') := by
  induction hreach with
  | zero => rfl
  | @step next steps cfg final hstep hrest ih =>
      have hcursor := htrans.cursorStep_commute_internal
        hstart hblank hstep
      have hstart' := output_startInvariant_step_internal hstart hstep
      have hblank' := htrans.output_blankAfterHead_step hblank hstep
      simp only [cursorTrace, hcursor]
      exact ih hstart' hblank'

theorem IsTransducer.cursorTraceObserved_commute_internal {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) :
    ∃ advances,
      tm.cursorTraceObserved steps (.ofCfg cfg) =
        some (.ofCfg cfg', advances) ∧
      cfg'.output.head = cfg.output.head + advances := by
  induction hreach with
  | zero =>
      exact ⟨0, rfl, by simp⟩
  | @step source next remaining final hstep hrest ih =>
      have hobserved := htrans.cursorStepObserved_commute_internal
        hstart hblank hstep
      have hhead := htrans.cursorStepObserved_head_internal hstart hstep
      have hstart' := output_startInvariant_step_internal hstart hstep
      have hblank' := htrans.output_blankAfterHead_step hblank hstep
      obtain ⟨later, hlater, hfinalHead⟩ := ih hstart' hblank'
      let advanced := (tm.cursorOutputEvent (.ofCfg source)).advance
      refine ⟨advanced + later, ?_, ?_⟩
      · simp only [cursorTraceObserved, hobserved, hlater,
          Option.bind_eq_bind, Option.bind_some, pure, advanced]
      · rw [hfinalHead, hhead]
        omega

theorem IsTransducer.cursorTraceObserved_initCfg_internal {tm : TM n}
    (htrans : tm.IsTransducer) {input : List Bool} {steps : ℕ}
    {cfg : Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg input) cfg) :
    tm.cursorTraceObserved steps (.ofCfg (tm.initCfg input)) =
      some (.ofCfg cfg, cfg.output.head) := by
  obtain ⟨advances, htrace, hhead⟩ :=
    htrans.cursorTraceObserved_commute_internal hreach
      Tape.StartInvariant.init_nil Tape.BlankAfterHead.init_nil
  have hadvances : advances = cfg.output.head := by
    simpa using hhead.symm
  simpa only [hadvances] using htrace

theorem IsTransducer.cursorTrace_initCfg_internal {tm : TM n}
    (htrans : tm.IsTransducer) {input : List Bool} {steps : ℕ}
    {cfg : Cfg n tm.Q}
    (hreach : tm.reachesIn steps (tm.initCfg input) cfg) :
    tm.cursorTrace steps (.ofCfg (tm.initCfg input)) =
      some (.ofCfg cfg) :=
  htrans.cursorTrace_commute_internal hreach
    Tape.StartInvariant.init_nil Tape.BlankAfterHead.init_nil

theorem suppressOutputTM_isTransducer_internal (tm : TM n) :
    (suppressOutputTM tm).IsTransducer := by
  intro state inputHead workHeads outputHead
  rcases state with ⟨source⟩ | ⟨⟩
  · rcases source with ⟨sourceState, cursor⟩
    simp only [suppressOutputTM]
    split
    · cases outputHead <;> simp [allReadBack, idleDir]
    · cases outputHead <;> simp [idleDir]
  · cases outputHead <;> simp [suppressOutputTM, allIdle, idleDir]

theorem suppressOutputTM_step_internal (tm : TM n)
    {cfg cfg' : CursorCfg n tm.Q} (realOutput : Tape)
    (hcursor : tm.cursorStep cfg = some cfg') :
    (suppressOutputTM tm).step (suppressOutputCfg tm cfg realOutput) =
      some (suppressOutputCfg tm cfg'
        (suppressOutputTapeStep realOutput)) := by
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
    simp [TM.step, suppressOutputTM, suppressOutputCfg,
      suppressOutputTapeStep, hhalt, htransition]

theorem suppressOutputTM_reachesIn_cursorTrace_internal (tm : TM n)
    {steps : ℕ} {cfg cfg' : CursorCfg n tm.Q} (realOutput : Tape)
    (htrace : tm.cursorTrace steps cfg = some cfg') :
    (suppressOutputTM tm).reachesIn steps
      (suppressOutputCfg tm cfg realOutput)
      (suppressOutputCfg tm cfg'
        (suppressOutputTapeTrace steps realOutput)) := by
  induction steps generalizing cfg realOutput with
  | zero =>
      simp only [cursorTrace, Option.some.injEq] at htrace
      subst cfg'
      exact .zero
  | succ steps ih =>
      simp only [cursorTrace] at htrace
      cases hstep : tm.cursorStep cfg with
      | none => simp [hstep] at htrace
      | some next =>
          simp only [hstep] at htrace
          exact .step (suppressOutputTM_step_internal tm realOutput hstep)
            (ih (suppressOutputTapeStep realOutput) htrace)

theorem IsTransducer.suppressOutputTM_reachesIn_internal {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) (realOutput : Tape) :
    (suppressOutputTM tm).reachesIn steps
      (suppressOutputCfg tm (.ofCfg cfg) realOutput)
      (suppressOutputCfg tm (.ofCfg cfg')
        (suppressOutputTapeTrace steps realOutput)) :=
  suppressOutputTM_reachesIn_cursorTrace_internal tm realOutput
    (htrans.cursorTrace_commute_internal hreach hstart hblank)

theorem suppressOutputTM_halt_step_internal (tm : TM n)
    (cfg : CursorCfg n tm.Q) (realOutput : Tape)
    (hhalt : cfg.state = tm.qhalt) :
    (suppressOutputTM tm).step (suppressOutputCfg tm cfg realOutput) =
      some (suppressOutputDoneCfg tm cfg realOutput) := by
  simp [TM.step, suppressOutputTM, suppressOutputCfg,
    suppressOutputDoneCfg, hhalt, allReadBack]

theorem IsTransducer.suppressOutputTM_reachesIn_halt_internal {tm : TM n}
    (htrans : tm.IsTransducer) {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg')
    (hstart : cfg.output.StartInvariant)
    (hblank : cfg.output.BlankAfterHead) (hhalt : tm.halted cfg')
    (realOutput : Tape) :
    (suppressOutputTM tm).reachesIn (steps + 1)
      (suppressOutputCfg tm (.ofCfg cfg) realOutput)
      (suppressOutputDoneCfg tm (.ofCfg cfg')
        (suppressOutputTapeTrace steps realOutput)) := by
  apply (suppressOutputTM tm).reachesIn_snoc
    (htrans.suppressOutputTM_reachesIn_internal hreach hstart hblank
      realOutput)
  exact suppressOutputTM_halt_step_internal tm _ _ hhalt

private theorem suppressOutputTapeStep_cells_internal {tape : Tape}
    (hstart : tape.StartInvariant) :
    (suppressOutputTapeStep tape).cells = tape.cells := by
  unfold suppressOutputTapeStep Tape.writeAndMove
  rw [Tape.move_cells]
  by_cases hhead : tape.head = 0
  · simp [Tape.write, hhead]
  · have hread : tape.read ≠ Γ.start := by
      exact hstart.2 tape.head (by omega)
    exact congrArg Tape.cells (write_readBack tape hread)

theorem suppressOutputTapeTrace_cells_internal (steps : ℕ) {tape : Tape}
    (hstart : tape.StartInvariant) :
    (suppressOutputTapeTrace steps tape).cells = tape.cells := by
  induction steps generalizing tape with
  | zero => rfl
  | succ steps ih =>
      rw [suppressOutputTapeTrace]
      have hstart' : (suppressOutputTapeStep tape).StartInvariant := by
        exact hstart.writeAndMove _ _
      calc
        (suppressOutputTapeTrace steps
          (suppressOutputTapeStep tape)).cells =
            (suppressOutputTapeStep tape).cells := ih hstart'
        _ = tape.cells := suppressOutputTapeStep_cells_internal hstart

private theorem suppressOutputTapeStep_eq_self_internal {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    suppressOutputTapeStep tape = tape := by
  rw [suppressOutputTapeStep]
  rw [writeAndMove_readBack tape hread]
  simp [idleDir, hread, Tape.move]

theorem suppressOutputTapeTrace_eq_self_internal (steps : ℕ) {tape : Tape}
    (hread : tape.read ≠ Γ.start) :
    suppressOutputTapeTrace steps tape = tape := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [suppressOutputTapeTrace,
        suppressOutputTapeStep_eq_self_internal hread, ih]

theorem suppressOutputTapeTrace_succ_init_internal (steps : ℕ) :
    suppressOutputTapeTrace (steps + 1) (Tape.init []) =
      (Tape.init []).move Dir3.right := by
  rw [suppressOutputTapeTrace]
  have hfirst : suppressOutputTapeStep (Tape.init []) =
      (Tape.init []).move Dir3.right := by
    simp [suppressOutputTapeStep, Tape.writeAndMove, Tape.write,
      Tape.read, Tape.move, Tape.init, idleDir]
  rw [hfirst]
  apply suppressOutputTapeTrace_eq_self_internal
  simp [Tape.read, Tape.move, Tape.init]

private theorem suppressOutputTapeTrace_startInvariant_internal
    (steps : ℕ) {tape : Tape} (hstart : tape.StartInvariant) :
    (suppressOutputTapeTrace steps tape).StartInvariant := by
  induction steps generalizing tape with
  | zero => exact hstart
  | succ steps ih =>
      rw [suppressOutputTapeTrace]
      exact ih (hstart.writeAndMove _ _)

theorem suppressOutputTapeTrace_init_hasOutput_nil_internal (steps : ℕ) :
    (suppressOutputTapeTrace steps (Tape.init [])).HasOutput [] := by
  rw [Tape.HasOutput]
  refine ⟨fun _ h => (by simp at h), ?_⟩
  rw [suppressOutputTapeTrace_cells_internal steps
    Tape.StartInvariant.init_nil]
  exact Tape.init_nil_cells_succ 0

private theorem suppressOutputDoneCfg_init_hasOutput_nil_internal
    (tm : TM n) (cfg : CursorCfg n tm.Q) (steps : ℕ) :
    (suppressOutputDoneCfg tm cfg
      (suppressOutputTapeTrace steps (Tape.init []))).output.HasOutput [] := by
  change (suppressOutputTapeStep
    (suppressOutputTapeTrace steps (Tape.init []))).HasOutput []
  have hstart := suppressOutputTapeTrace_startInvariant_internal steps
    Tape.StartInvariant.init_nil
  rw [Tape.HasOutput]
  refine ⟨fun _ h => (by simp at h), ?_⟩
  rw [suppressOutputTapeStep_cells_internal hstart,
    suppressOutputTapeTrace_cells_internal steps
      Tape.StartInvariant.init_nil]
  exact Tape.init_nil_cells_succ 0

theorem IsTransducer.suppressOutputTM_computesNil_internal {tm : TM n}
    {f : List Bool → List Bool} {T : ℕ → ℕ}
    (htrans : tm.IsTransducer) (hcomp : tm.ComputesInTime f T) :
    (suppressOutputTM tm).ComputesInTime (fun _ => [])
      (fun inputLength => T inputLength + 1) := by
  intro input
  obtain ⟨cfg, steps, hsteps, hreach, hhalt, _hout⟩ := hcomp input
  let finalCfg := suppressOutputDoneCfg tm (.ofCfg cfg)
    (suppressOutputTapeTrace steps (Tape.init []))
  refine ⟨finalCfg, steps + 1, Nat.add_le_add_right hsteps 1, ?_, ?_, ?_⟩
  · simpa [finalCfg, suppressOutputTM, suppressOutputCfg,
      CursorCfg.ofCfg, Tape.outputCursor] using
      htrans.suppressOutputTM_reachesIn_halt_internal hreach
        Tape.StartInvariant.init_nil Tape.BlankAfterHead.init_nil hhalt
        (Tape.init [])
  · rfl
  · exact suppressOutputDoneCfg_init_hasOutput_nil_internal tm
      (.ofCfg cfg) steps

end TM

end Complexity
