/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Complexitylib.Models.TuringMachine.Subroutines.PairBuild

/-!
# Public pair-builder API checks

Run with `lake env lean scripts/PairBuildApiCheck.lean`.
The only import is the supported model-layer surface. These kernel checks
preserve the concrete machine, exact bound, initialized-tape postcondition,
NTM lift, and frame theorem availability. No NP or SAT import is needed.
-/

namespace Complexity

example (xLen yLen : ℕ) : TM.pairBuildTime xLen yLen = 4 * xLen + 2 * yLen + 10 := rfl
example : TM.pairBuildTime 0 0 = 10 := rfl
example : pair [] [] = [false, true] := rfl
example : pair [true] [false] = [true, true, false, true, false] := rfl

example (yIdx pIdx : Fin k) : (TM.pairBuildTM yIdx pIdx).Q = TM.PairBuildPhase := rfl
example (yIdx pIdx : Fin k) : (TM.pairBuildTM yIdx pIdx).qstart = .init := rfl
example (yIdx pIdx : Fin k) : (TM.pairBuildTM yIdx pIdx).qhalt = .done := rfl
example : Fintype TM.PairBuildPhase := inferInstance

example (yIdx pIdx : Fin k) (hne : yIdx ≠ pIdx) (x y : List Bool) :
    (TM.pairBuildTM yIdx pIdx).HoareTime
      (fun inp work _ =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work yIdx = Tape.init (y.map Γ.ofBool) ∧
        work pIdx = Tape.init [])
      (fun _ work _ =>
        work pIdx = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
      (TM.pairBuildTime x.length y.length) :=
  TM.pairBuildTM_hoareTime_initTape_move_right yIdx pIdx hne x y

#check TM.pairBuild_init_step_started
#check TM.pairBuild_init_step_all_started
#check TM.Tape.eq_init_move_right_of_binary
#check TM.pairBuildTM_hoareTime
#check TM.pairBuildTM_hoareTime_all_started_initTape_move_right
#check TM.pairBuildTM_toNTM_hoareTime_all_started_initTape_move_right
#check TM.pairBuildTM_trace_one_preserves_output
#check TM.pairBuildTM_trace_preserves_output
#check TM.pairBuildTM_trace_one_preserves_other_work
#check TM.pairBuildTM_trace_preserves_other_work
#check TM.pairBuildTM_hoareTime_hasOutput

end Complexity
