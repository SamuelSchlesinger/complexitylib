/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.Core.Defs
public import Complexitylib.Models.TuringMachine.Hoare

/-!
# Circuit-evaluator staging seam

This file connects the valid outer-pair staging contract to the streaming
core's precondition across the standard sequential-composition tape transition.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

namespace Internal

/-- A valid pair-staging endpoint supplies the streaming core's exact tape
precondition after the standard sequential-composition transition. The staged
input tape is stable and becomes the core's explicit input frame. -/
theorem pairStagePost_pair_familyCorePre (codeBits inputBits : List Bool)
    (inp : Tape) (work : Fin workTapeCount → Tape) (out : Tape)
    (hpost : PairStagePost (pair codeBits inputBits) inp work out) :
    FamilyCorePre codeBits inputBits inp (TM.transitionInput inp)
      (fun i => TM.transitionTape (work i)) (TM.transitionTape out) := by
  unfold PairStagePost at hpost
  rcases hpost with
    ⟨hinputCells, houtputHead, houtputInv, hresult⟩
  simp only [unpair?_pair] at hresult
  rcases hresult with
    ⟨hinputHead, hcodeZero, hcodePrefix, hwiresZero, hwiresPrefix,
      hcounter, _⟩
  have hinputRead : inp.read ≠ Γ.start := by
    rw [Tape.read, hinputHead, hinputCells]
    exact Tape.init_ofBool_cells_ne_start (pair codeBits inputBits)
      ((pair codeBits inputBits).length + 1) (by omega)
  have hcodeRead : (work codeIdx).read ≠ Γ.start := by
    have hblank := hcodePrefix.2.2 codeBits.length le_rfl
    rw [Tape.read, hcodePrefix.1, hblank]
    decide
  have hwiresRead : (work wiresIdx).read ≠ Γ.start := by
    have hblank := hwiresPrefix.2.2 inputBits.length le_rfl
    rw [Tape.read, hwiresPrefix.1, hblank]
    decide
  have hcounterRead : (work counterIdx).read ≠ Γ.start := by
    rw [hcounter]
    simp [Tape.read, Tape.move, Tape.init]
  have houtputRead : out.read ≠ Γ.start :=
    houtputInv.read_ne_start (by omega)
  have hinputStable := TM.transitionInput_eq_self hinputRead
  have hcodeStable := TM.transitionTape_eq_self hcodeRead
  have hwiresStable := TM.transitionTape_eq_self hwiresRead
  have hcounterStable := TM.transitionTape_eq_self hcounterRead
  have houtputStable := TM.transitionTape_eq_self houtputRead
  unfold FamilyCorePre
  dsimp only
  rw [hinputStable, hcodeStable, hwiresStable, hcounterStable,
    houtputStable]
  exact ⟨rfl, hinputRead, hcodeZero, hcodePrefix, hwiresZero,
    hwiresPrefix, hcounter, houtputHead, houtputInv⟩

end Internal

end Machine

end CircuitCode

end Complexity
