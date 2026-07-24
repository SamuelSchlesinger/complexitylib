/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators

/-!
# Resuming a machine after its sentinel transition -- definitions

Every nonhalted machine takes one forced first transition while all tape heads
read `▷`. Phase composition usually enters a component with those heads already
parked at cell one. `TM.startedTM` keeps the source transition function and halt
state but uses the post-sentinel control state as its start state.
-/

namespace Complexity

namespace TM

/-- The source control state reached by its all-sentinel transition. -/
def startedState (tm : TM n) : tm.Q :=
  (tm.δ tm.qstart Γ.start (fun _ => Γ.start) Γ.start).1

/-- A source machine resumed after its compulsory all-sentinel transition.
The transition function and halt state are unchanged. If the source already
starts halted, so does the wrapper. -/
def startedTM (tm : TM n) : TM n where
  Q := tm.Q
  qstart := if tm.qstart = tm.qhalt then tm.qhalt else tm.startedState
  qhalt := tm.qhalt
  δ := tm.δ
  δ_right_of_start := tm.δ_right_of_start

end TM

end Complexity
