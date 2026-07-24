/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.Started.Defs
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Resuming a machine after its sentinel transition -- proof internals
-/

namespace Complexity

namespace TM

theorem startedTM_step_eq_internal (tm : TM n) (cfg : Cfg n tm.Q) :
    tm.startedTM.step cfg = tm.step cfg := by
  rfl

theorem startedTM_reachesIn_of_source_internal (tm : TM n)
    {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg') :
    tm.startedTM.reachesIn steps cfg cfg' := by
  induction hreach with
  | zero => exact .zero
  | step hstep _ ih =>
      exact .step (by rw [startedTM_step_eq_internal]; exact hstep) ih

theorem source_reachesIn_of_startedTM_internal (tm : TM n)
    {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.startedTM.reachesIn steps cfg cfg') :
    tm.reachesIn steps cfg cfg' := by
  apply reachesIn_map (tm := tm.startedTM) (tm' := tm)
    (fun cfg => cfg) _ hreach
  intro before after hstep
  rw [← startedTM_step_eq_internal]
  exact hstep

theorem startedTM_qstart_eq_startedState_internal (tm : TM n)
    (hne : tm.qstart ≠ tm.qhalt) :
    tm.startedTM.qstart = tm.startedState := by
  simp [startedTM, hne]

theorem IsTransducer.startedTM_internal {tm : TM n}
    (htrans : tm.IsTransducer) : tm.startedTM.IsTransducer := by
  intro state inputHead workHeads outputHead
  exact htrans state inputHead workHeads outputHead

end TM

end Complexity
