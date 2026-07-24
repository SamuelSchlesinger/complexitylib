/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Lift

/-!
# Output-retargeting frames -- definitions

`retargetOutput` redirects a machine's virtual output onto a fresh work tape.
The standard embedding uses a blank real output; this variant carries an
arbitrary real-output frame for composition inside an output accumulator.
-/

namespace Complexity

namespace TM

/-- Embed a source configuration into `retargetOutput` while carrying an
arbitrary real output tape. -/
def retargetCfgFrame (tm : TM n) (cfg : Cfg n tm.Q) (output : Tape) :
    Cfg (n + 1) tm.Q where
  state := cfg.state
  input := cfg.input
  work := fun i => if h : i.val < n then cfg.work ⟨i.val, h⟩ else cfg.output
  output := output

end TM

end Complexity
