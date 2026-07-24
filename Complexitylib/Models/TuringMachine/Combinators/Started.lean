/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.Started.Defs
import Complexitylib.Models.TuringMachine.Combinators.Started.Internal

/-!
# Resuming a machine after its sentinel transition

`TM.startedTM` gives phase composition a reusable way to enter an ordinary
machine after its compulsory first transition from the all-`▷` configuration.
It changes only the start state; concrete stepping, halting, and the transducer
discipline are inherited exactly.

## Main results

- `TM.startedTM_step_eq` -- started and source concrete steps are identical.
- `TM.startedTM_reachesIn_of_source` -- source runs transfer unchanged.
- `TM.source_reachesIn_of_startedTM` -- started runs transfer back unchanged.
- `TM.IsTransducer.startedTM` -- one-way output safety is preserved.
-/

namespace Complexity

namespace TM

/-- The started wrapper and source have identical concrete step functions. -/
theorem startedTM_step_eq (tm : TM n) (cfg : Cfg n tm.Q) :
    tm.startedTM.step cfg = tm.step cfg :=
  startedTM_step_eq_internal tm cfg

/-- Every exact source run is an exact run of the started wrapper from the
same configuration. -/
theorem startedTM_reachesIn_of_source (tm : TM n)
    {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.reachesIn steps cfg cfg') :
    tm.startedTM.reachesIn steps cfg cfg' :=
  startedTM_reachesIn_of_source_internal tm hreach

/-- Every exact started-wrapper run is an exact source run from the same
configuration. -/
theorem source_reachesIn_of_startedTM (tm : TM n)
    {steps : ℕ} {cfg cfg' : Cfg n tm.Q}
    (hreach : tm.startedTM.reachesIn steps cfg cfg') :
    tm.reachesIn steps cfg cfg' :=
  source_reachesIn_of_startedTM_internal tm hreach

/-- A nonhalted source gives the wrapper exactly its post-sentinel control
state. -/
theorem startedTM_qstart_eq_startedState (tm : TM n)
    (hne : tm.qstart ≠ tm.qhalt) :
    tm.startedTM.qstart = tm.startedState :=
  startedTM_qstart_eq_startedState_internal tm hne

/-- Resuming after the sentinel transition preserves append-only output. -/
theorem IsTransducer.startedTM {tm : TM n}
    (htrans : tm.IsTransducer) : tm.startedTM.IsTransducer :=
  htrans.startedTM_internal

end TM

end Complexity
