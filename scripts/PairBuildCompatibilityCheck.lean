/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Classes.NP.Internal.PairBuildTM

/-!
# Legacy pair-builder import compatibility

Run with `lake build --wfail PairBuildCompatibilityCheck`.
A module-style client of the old import path retains the same transparent
machine, exact bound, instance, helpers, and correctness theorems.
-/

namespace Complexity

example (xLen yLen : ℕ) : TM.pairBuildTime xLen yLen = 4 * xLen + 2 * yLen + 10 := rfl
example (yIdx pIdx : Fin k) : (TM.pairBuildTM yIdx pIdx).Q = TM.PairBuildPhase := rfl
example (yIdx pIdx : Fin k) : (TM.pairBuildTM yIdx pIdx).qstart = .init := rfl
example (yIdx pIdx : Fin k) : (TM.pairBuildTM yIdx pIdx).qhalt = .done := rfl
example : Fintype TM.PairBuildPhase := inferInstance

#check TM.pairBuild_init_step_started
#check TM.pairBuild_init_step_all_started
#check TM.Tape.eq_init_move_right_of_binary
#check TM.pairBuildTM_hoareTime
#check TM.pairBuildTM_hoareTime_initTape_move_right
#check TM.pairBuildTM_hoareTime_all_started_initTape_move_right
#check TM.pairBuildTM_toNTM_hoareTime_all_started_initTape_move_right
#check TM.pairBuildTM_trace_one_preserves_output
#check TM.pairBuildTM_trace_preserves_output
#check TM.pairBuildTM_trace_one_preserves_other_work
#check TM.pairBuildTM_trace_preserves_other_work
#check TM.pairBuildTM_hoareTime_hasOutput

end Complexity
