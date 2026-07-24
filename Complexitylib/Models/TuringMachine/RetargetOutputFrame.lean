/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.RetargetOutputFrame.Internal

/-!
# Output-retargeting frames

These lemmas let a retargeted machine carry an arbitrary parked real-output
accumulator while its virtual output evolves on the fresh final work tape.
-/

namespace Complexity

namespace TM

@[simp] theorem retargetCfgFrame_state (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    (tm.retargetCfgFrame cfg output).state = cfg.state :=
  retargetCfgFrame_state_internal tm cfg output

@[simp] theorem retargetCfgFrame_input (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    (tm.retargetCfgFrame cfg output).input = cfg.input :=
  retargetCfgFrame_input_internal tm cfg output

@[simp] theorem retargetCfgFrame_output (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    (tm.retargetCfgFrame cfg output).output = output :=
  retargetCfgFrame_output_internal tm cfg output

theorem retargetCfgFrame_work_lt (tm : TM n) (cfg : Cfg n tm.Q)
    (output : Tape) (i : Fin (n + 1)) (hi : i.val < n) :
    (tm.retargetCfgFrame cfg output).work i = cfg.work ⟨i.val, hi⟩ :=
  retargetCfgFrame_work_lt_internal tm cfg output i hi

theorem retargetCfgFrame_work_last (tm : TM n) (cfg : Cfg n tm.Q)
    (output : Tape) :
    (tm.retargetCfgFrame cfg output).work (Fin.last n) = cfg.output :=
  retargetCfgFrame_work_last_internal tm cfg output

/-- A parked real output is a literal frame for one retargeted step. -/
theorem retargetOutput_step_retargetCfgFrame (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) (houtput : Parked output) :
    tm.retargetOutput.step (tm.retargetCfgFrame cfg output) =
      (tm.step cfg).map fun next => tm.retargetCfgFrame next output :=
  retargetOutput_step_retargetCfgFrame_internal tm cfg output houtput

/-- A parked real output remains literally fixed throughout a retargeted run. -/
theorem retargetOutput_reachesIn_retargetCfgFrame (tm : TM n)
    (output : Tape) (houtput : Parked output) {steps : ℕ}
    {start done : Cfg n tm.Q} (hreach : tm.reachesIn steps start done) :
    tm.retargetOutput.reachesIn steps
      (tm.retargetCfgFrame start output) (tm.retargetCfgFrame done output) :=
  retargetOutput_reachesIn_retargetCfgFrame_internal tm output houtput hreach

/-- Retargeting preserves a source all-prefix auxiliary-space certificate when
the source's final virtual-output head fits in that same budget. -/
theorem IsTransducer.retargetOutput_reachesIn_retargetCfgFrame_withinAuxSpace
    {tm : TM n} (htrans : tm.IsTransducer)
    (output : Tape) (houtput : Parked output)
    {steps inputLength space : ℕ} {start done : Cfg n tm.Q}
    (hreach : tm.reachesIn steps start done)
    (hprefix : ∀ elapsed cfg, elapsed ≤ steps →
      tm.reachesIn elapsed start cfg →
      cfg.WithinAuxSpace inputLength space)
    (hdoneOutput : done.output.head ≤ space) :
    tm.retargetOutput.reachesIn steps
        (tm.retargetCfgFrame start output)
        (tm.retargetCfgFrame done output) ∧
      ∀ elapsed cfg, elapsed ≤ steps →
        tm.retargetOutput.reachesIn elapsed
          (tm.retargetCfgFrame start output) cfg →
        cfg.WithinAuxSpace inputLength space :=
  htrans.retargetOutput_reachesIn_retargetCfgFrame_withinAuxSpace_internal
    output houtput hreach hprefix hdoneOutput

@[simp] theorem retargetOutput_halted_retargetCfgFrame (tm : TM n)
    (cfg : Cfg n tm.Q) (output : Tape) :
    tm.retargetOutput.halted (tm.retargetCfgFrame cfg output) ↔
      tm.halted cfg :=
  retargetOutput_halted_retargetCfgFrame_internal tm cfg output

end TM

end Complexity
