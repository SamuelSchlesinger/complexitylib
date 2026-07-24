/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbe.Defs
import Complexitylib.Models.TuringMachine.OutputProbe.Internal

/-!
# Random-access probes for append-only transducer output

`TM.outputProbeTM` adds one canonical binary countdown tape to a source
transducer. The source output is represented only by `TM.OutputCursor`. A
right output move decrements the countdown with the verified binary
predecessor machine; once it reaches zero, leaving the selected ordinary cell
captures the finalized bit. A source halt on that cell captures the cursor's
current bit. The physical output tape receives only the one-bit answer.

This is the executable recomputation kernel needed for log-space composition:
the potentially polynomial source output is never copied to work tape, while
the requested position occupies only its binary width.

## Main results

- `TM.outputProbeTM_isTransducer` -- the probe retains append-only output.
- `TM.IsTransducer.outputProbeTM_step_startedCfg` -- the compulsory first
  probe transition reaches the canonical restartable entry configuration.
- `TM.outputProbeTM_step_source` -- exact simulation of one source step.
- `TM.outputProbeTM_reachesIn_source_not_right` -- a non-right source step
  preserves the countdown.
- `TM.outputProbeTM_reachesIn_source_positive` -- a right source step followed
  by verified binary predecessor decrements a positive countdown.
- `TM.outputProbeTM_source_positive_prefix_withinAuxSpace` -- every prefix of
  that countdown invocation uses only the represented binary width.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved` -- an entire observed
  source run consumes exactly its counted output advances.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace` -- the
  entire replay has an all-prefix source-space-plus-binary-width bound.
- `TM.outputProbeTM_step_halt_capture` -- zero countdown at a halted Boolean
  cursor selects that bit for physical output.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved_capture` -- end-to-end
  replay and one-bit output when the selected frontier cell is final.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved_capture_init` -- the same
  theorem from canonical blank physical output, with no tape-shape premises.
- `TM.outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture` -- the
  corresponding end-to-end theorem for a cell finalized before source halt.
- `TM.IsTransducer.outputProbeTM_reachesIn_getElem` -- any valid output index
  of a successful concrete transducer run can be captured.
- `TM.ComputesInSpace.outputProbeTM_getElem` -- the same valid-index interface
  for an abstract space-bounded function computation.
- `TM.ComputesInSpace.outputProbeTM_getElem_withinAuxSpace` -- the valid-index
  query with an all-prefix space certificate through capture.
- `TM.ComputesInSpace.outputProbeTM_index_halts_withinAuxSpace` -- every
  positive-position query terminates with a Boolean result and the same
  all-prefix bound, including blank and beyond-frontier positions.
- `TM.ComputesInSpace.outputProbeStartedTM_getElem` -- the valid-index query
  from the canonical post-sentinel frame used by phase composition.
- `TM.ComputesInSpace.outputProbeStartedTM_getElem_withinAuxSpace` -- the
  restartable query with the same all-prefix certificate.
- `TM.ComputesInSpace.outputProbeStartedRetargetTM_getElem` -- the same query
  with the captured bit redirected to a fresh work tape.
- `TM.ComputesInSpace.outputProbeStartedRetargetTM_getElem_withinAuxSpace` --
  the retargeted query with all physical work tapes covered by the bound.
- `TM.ComputesInSpace.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace`
  -- the same query inside an arbitrary stable controller-tape frame.
- `TM.outputProbeSourceResultCfg_capture` -- a right move with a zero
  countdown selects the finalized bit for capture.
- `TM.outputProbeTM_capture_hasOutput` -- capture reaches the unique halt state
  with exactly the selected one-bit output.
-/

namespace Complexity

namespace TM

/-- The output-position probe never moves its physical output head left. -/
theorem outputProbeTM_isTransducer (tm : TM n) :
    (outputProbeTM tm).IsTransducer :=
  outputProbeTM_isTransducer_internal tm

/-- The compulsory first probe transition reaches the canonical restartable
entry configuration, with every owned tape parked at cell one. -/
theorem IsTransducer.outputProbeTM_step_startedCfg
    {tm : TM n} (htrans : tm.IsTransducer) (input : List Bool)
    (value : ℕ) (hne : tm.qstart ≠ tm.qhalt) :
    (outputProbeTM tm).step
      (outputProbeCfg tm (.ofCfg (tm.initCfg input))
        (outputProbeCounterTape value) (Tape.init [])) =
      some (outputProbeStartedCfg tm input
        (outputProbeCounterTape value)) :=
  htrans.outputProbeTM_step_startedCfg_internal input value hne

/-- One probe source-phase step implements one finite-cursor source step. The
source input/work actions are exact, the countdown is preserved during this
transition, and the independent physical output performs its idle action. -/
theorem outputProbeTM_step_source (tm : TM n)
    {cfg cfg' : CursorCfg n tm.Q} (counter output : Tape)
    (hcounter : counter.read ≠ Γ.start)
    (hcursor : tm.cursorStep cfg = some cfg') :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeSourceResultCfg tm cfg cfg' counter
        (suppressOutputTapeStep output)) :=
  outputProbeTM_step_source_internal tm counter output hcounter hcursor

/-- A source step whose logical output head does not move right takes one
probe transition and preserves the binary countdown exactly. -/
theorem outputProbeTM_reachesIn_source_not_right (tm : TM n)
    {before after : CursorCfg n tm.Q} (counter output : Tape)
    (hcursor : tm.cursorStep before = some after)
    (hdir : tm.cursorOutputDirection before ≠ Dir3.right)
    (hcounter : counter.read ≠ Γ.start) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCfg tm before counter output)
      (outputProbeCfg tm after counter
        (suppressOutputTapeStep output)) :=
  outputProbeTM_reachesIn_source_not_right_internal tm counter output
    hcursor hdir hcounter

/-- A right-moving source step followed by marker normalization, the verified
binary predecessor, and exact marker restoration changes a canonical positive
countdown `value + 1` to canonical `value`. The source configuration after its
one step is retained exactly, even when its input or work heads rest on `▷`. -/
theorem outputProbeTM_reachesIn_source_positive (tm : TM n)
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
        (suppressOutputTapeStep output)) :=
  outputProbeTM_reachesIn_source_positive_internal tm counter output
    hcursor hdir hcounter hinput hwork houtput

/-- Every prefix of one positive-countdown source invocation stays inside the
initial auxiliary-space budget plus the represented counter's binary width
and a constant seam allowance. -/
theorem outputProbeTM_source_positive_prefix_withinAuxSpace
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
      (outputProbePositiveSpace initialSpace value) :=
  outputProbeTM_source_positive_prefix_withinAuxSpace_internal tm
    counter output hinitial hprefix hreach

/-- When the countdown is canonical zero, leaving an ordinary source-output
cell to the right selects the just-written Boolean symbol for capture. -/
theorem outputProbeSourceResultCfg_capture (tm : TM n)
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
        output :=
  outputProbeSourceResultCfg_capture_internal tm before after counter output
    bit symbol hcursor hdir hwrite hcounter

/-- An entire finite-cursor source run can be replayed by the concrete probe
without materializing its output. If the initial counter is `remaining` plus
the run's observed frontier advances, the final counter is canonical
`remaining`; the source input/work configuration is retained exactly. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved (tm : TM n)
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
          (suppressOutputTapeTrace steps output)) :=
  outputProbeTM_reachesIn_cursorTraceObserved_internal tm counter output
    htrace hinput hwork hcounter houtput

/-- Replay an observed source run with an all-prefix auxiliary-space bound.
`Inv` may be any source invariant preserved by cursor steps whose input and
work heads stay inside `sourceSpace`. The probe adds only the binary width of
the initial countdown, independently of the number of predecessor calls. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace
    (tm : TM n) (Inv : CursorCfg n tm.Q → Prop)
    {steps advances remaining inputLength sourceSpace : ℕ}
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
    (houtput : output.StartInvariant) :
    ∃ probeSteps,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter output)
        (outputProbeCfg tm after (outputProbeCounterTape remaining)
          (suppressOutputTapeTrace steps output)) ∧
      ∀ elapsed cfg, elapsed ≤ probeSteps →
        (outputProbeTM tm).reachesIn elapsed
          (outputProbeCfg tm before counter output) cfg →
        cfg.WithinAuxSpace inputLength
          (outputProbeReplaySpace sourceSpace (remaining + advances)) :=
  outputProbeTM_reachesIn_cursorTraceObserved_withinAuxSpace_internal tm
    Inv counter output htrace hinv hinvStep hinvSpace hsourceSpace hinput
    hwork hcounter houtput le_rfl

/-- At a halted source state, a canonical zero countdown and Boolean cursor
select that cursor bit for capture. The normalization action is explicit so
the theorem applies even when source heads are parked on `▷`. -/
theorem outputProbeTM_step_halt_capture (tm : TM n)
    (cfg : CursorCfg n tm.Q) (counter output : Tape) (bit : Bool)
    (hhalt : cfg.state = tm.qhalt)
    (hcursor : cfg.output = .cell (Γ.ofBool bit))
    (hcounter : counter.HasBinaryNat 0) :
    (outputProbeTM tm).step (outputProbeCfg tm cfg counter output) =
      some (outputProbeCaptureCfg tm bit
        (outputProbeNormalizeInput cfg.input)
        (outputProbeNormalizeWork fun i =>
          if h : i.val < n then cfg.work ⟨i.val, h⟩ else counter)
        (outputProbeNormalizeTape output)) :=
  outputProbeTM_step_halt_capture_internal tm cfg counter output bit
    hhalt hcursor hcounter

/-- From a blank physical output parked at cell one, the capture phase takes
one transition to the unique probe halt state and exposes exactly `[bit]` as
its output string. -/
theorem outputProbeTM_capture_hasOutput (tm : TM n) (bit : Bool)
    (input : Tape) (work : Fin (n + 1) → Tape) (output : Tape)
    (hhead : output.head = 1)
    (hcells : output.cells = (Tape.init []).cells) :
    (outputProbeTM tm).reachesIn 1
      (outputProbeCaptureCfg tm bit input work output)
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeTM tm).halted
      (outputProbeDoneCfg tm bit input work output) ∧
    (outputProbeDoneCfg tm bit input work output).output.HasOutput [bit] :=
  outputProbeTM_capture_hasOutput_internal tm bit input work output
    hhead hcells

/-- Replay an entire observed source run and emit its selected final frontier
bit. The initial countdown equals the run's exact number of output advances;
the source must halt with the Boolean bit under its cursor. The two physical
output hypotheses state that suppressed execution left the blank output parked
at cell one, as it does for every positive-length run from `Tape.init []`. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_capture (tm : TM n)
    {steps advances : ℕ}
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
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] :=
  outputProbeTM_reachesIn_cursorTraceObserved_capture_internal tm counter
    output bit htrace hinput hwork hcounter houtput hhalt hcursor
    hphysicalHead hphysicalCells

/-- Positive-length specialization of
`outputProbeTM_reachesIn_cursorTraceObserved_capture` from canonical blank
physical output. Suppressed execution parks that output at cell one and leaves
its cells unchanged, so callers need no physical-tape side conditions. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_capture_init (tm : TM n)
    {steps advances : ℕ}
    {before after : CursorCfg n tm.Q} (counter : Tape) (bit : Bool)
    (htrace : tm.cursorTraceObserved (steps + 1) before =
      some (after, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (hhalt : after.state = tm.qhalt)
    (hcursor : after.output = .cell (Γ.ofBool bit)) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter (Tape.init [])) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] :=
  outputProbeTM_reachesIn_cursorTraceObserved_capture tm counter
    (Tape.init []) bit htrace hinput hwork hcounter
    Tape.StartInvariant.init_nil hhalt hcursor
    (suppressOutputTapeTrace_succ_init_head steps)
    (suppressOutputTapeTrace_succ_init_cells steps)

/-- Replay an observed source prefix and emit the bit finalized by its next
right output move. This is the earlier-cell counterpart of
`outputProbeTM_reachesIn_cursorTraceObserved_capture`: together the two
theorems cover capture either when a cell is left or when the source halts on
the selected frontier cell. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture
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
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] :=
  outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_internal tm
    counter output bit symbol htrace hinput hwork hcounter houtput hnext
    hcursor hdir hwrite hphysicalHead hphysicalCells

/-- Positive-length specialization of the earlier-finalized-cell theorem from
canonical blank physical output. -/
theorem outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture_init
    (tm : TM n) {steps advances : ℕ}
    {before selected next : CursorCfg n tm.Q}
    (counter : Tape) (bit : Bool) (symbol : Γ)
    (htrace : tm.cursorTraceObserved (steps + 1) before =
      some (selected, advances))
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, (before.work i).StartInvariant)
    (hcounter : counter.HasBinaryNat advances)
    (hnext : tm.cursorStep selected = some next)
    (hcursor : selected.output = .cell symbol)
    (hdir : tm.cursorOutputDirection selected = Dir3.right)
    (hwrite : tm.cursorOutputWrite selected =
      if bit then Γw.one else Γw.zero) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm before counter (Tape.init [])) done ∧
      (outputProbeTM tm).halted done ∧ done.output.HasOutput [bit] :=
  outputProbeTM_reachesIn_cursorTraceObserved_finalize_capture tm counter
    (Tape.init []) bit symbol htrace hinput hwork hcounter
    Tape.StartInvariant.init_nil hnext hcursor hdir hwrite
    (suppressOutputTapeTrace_succ_init_head steps)
    (suppressOutputTapeTrace_succ_init_cells steps)

/-- Replay a successful complete transducer run to capture any valid output
index. The theorem hides whether the selected cell was finalized by an earlier
right move or remained under the source head at halt. -/
theorem IsTransducer.outputProbeTM_reachesIn_getElem
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
      done.output.HasOutput [bits[index]'hindex] :=
  htrans.outputProbeTM_reachesIn_getElem_internal
    hreach hhalt hout index hindex

/-- Every valid output index of a space-bounded function transducer is
captured by its concrete output probe from the canonical source input and
binary position tape. -/
theorem ComputesInSpace.outputProbeTM_getElem
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      (outputProbeTM tm).reachesIn probeSteps
        (outputProbeCfg tm (.ofCfg (tm.initCfg input))
          (outputProbeCounterTape (index + 1)) (Tape.init [])) done ∧
      (outputProbeTM tm).halted done ∧
      done.output.HasOutput [(f input)[index]'hindex] :=
  hcomp.outputProbeTM_getElem_internal input index hindex

/-- Every prefix of a valid output-bit query stays within the source space
plus the binary index width and the constant capture seam. The query consumes
its countdown exactly, leaving the canonical zero tape for reuse. -/
theorem ComputesInSpace.outputProbeTM_getElem_withinAuxSpace
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
            (index + 1)) :=
  hcomp.outputProbeTM_getElem_withinAuxSpace_internal input index hindex

/-- Every output-position query terminates with one Boolean result. Valid
indices retain the stronger exact theorem above; blank cells and positions
beyond the source frontier return zero. Every execution prefix satisfies the
same source-space-plus-binary-index bound. -/
theorem ComputesInSpace.outputProbeTM_index_halts_withinAuxSpace
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
            (index + 1)) :=
  hcomp.outputProbeTM_index_halts_withinAuxSpace_internal input index

/-- The canonical post-sentinel probe is total at every numeric output
position and preserves the complete all-prefix space certificate. -/
theorem ComputesInSpace.outputProbeStartedTM_index_halts_withinAuxSpace
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
            (index + 1)) :=
  hcomp.outputProbeStartedTM_index_halts_withinAuxSpace_internal input index

/-- Retargeting a total restartable query exposes one Boolean on a fresh work
tape, preserves a blank-support envelope for cleanup, and keeps the real output
parked. -/
theorem
    ComputesInSpace.outputProbeStartedRetargetTM_index_halts_withinAuxSpace
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
            (index + 1)) :=
  hcomp.outputProbeStartedRetargetTM_index_halts_withinAuxSpace_internal
    input index

/-- A total retargeted query preserves its Boolean result and cleanup support
when placed inside an arbitrary stable controller frame. -/
theorem
    ComputesInSpace.placeOutputProbeStartedRetargetTM_index_halts_withinAuxSpace
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
            frameSpace) :=
  hcomp.placeOutputProbeStartedRetargetTM_index_halts_withinAuxSpace_internal
    pre post input index extras hextra hframe

/-- Every valid output index of a space-bounded transducer can be queried from
the canonical post-sentinel frame. This removes the one compulsory source
transition that a caller has already paid at the enclosing machine boundary. -/
theorem ComputesInSpace.outputProbeStartedTM_getElem
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space) (input : List Bool)
    (index : ℕ) (hindex : index < (f input).length) :
    ∃ probeSteps done,
      (outputProbeStartedTM tm).reachesIn probeSteps
        (outputProbeStartedCfg tm input
          (outputProbeCounterTape (index + 1))) done ∧
      (outputProbeStartedTM tm).halted done ∧
      done.output.HasOutput [(f input)[index]'hindex] :=
  hcomp.outputProbeStartedTM_getElem_internal input index hindex

/-- The post-sentinel valid-index query retains the complete all-prefix
auxiliary-space certificate and leaves its countdown at canonical zero. -/
theorem ComputesInSpace.outputProbeStartedTM_getElem_withinAuxSpace
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
            (index + 1)) :=
  hcomp.outputProbeStartedTM_getElem_withinAuxSpace_internal
    input index hindex

/-- Redirecting the restartable query writes its captured bit on the fresh
last work tape and leaves the enclosing machine's real output parked blank. -/
theorem ComputesInSpace.outputProbeStartedRetargetTM_getElem
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
      done.output = (Tape.init []).move Dir3.right :=
  hcomp.outputProbeStartedRetargetTM_getElem_internal input index hindex

/-- Redirecting a restartable valid-index query to a fresh work tape covers
that tape, all source tapes, and every intermediate configuration with the
same explicit auxiliary-space budget. Its physical countdown tape is restored
to canonical zero. -/
theorem ComputesInSpace.outputProbeStartedRetargetTM_getElem_withinAuxSpace
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
            (index + 1)) :=
  hcomp.outputProbeStartedRetargetTM_getElem_withinAuxSpace_internal
    input index hindex

/-- Place a restartable retargeted query between persistent controller tapes.
The stable frame is preserved exactly, its largest head is charged alongside
the query budget, the captured bit remains available at the corresponding
physical work-tape index, and the placed countdown is canonical zero. -/
theorem ComputesInSpace.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace
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
            frameSpace) :=
  hcomp.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace_internal
    pre post input index hindex extras hextra hframe

end TM

end Complexity
