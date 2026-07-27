/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Next
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List

/-!
# Packed-step generator soundness

Soundness proofs for the compositional formula and delayed-copy routines used
by one direct-unrolling transition step.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem setStepPositionLimit_sound_for_step (extra : ℕ) :
    (setStepPositionLimit extra).Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.limit₁
    Work.copyCounter).seq (BinaryRoutine.addConst_sound Work.limit₁ extra)

private theorem emitStepImmutableCellCopies_sound_for_step :
    emitStepImmutableCellCopies.Sound :=
  BinaryRoutine.repeatRoutine_sound 4
    (emitPackedFormulaCopy (Polynomial.C 1))
    (emitPackedFormulaCopy_sound (Polynomial.C 1))

theorem emitStepStateFormulas_sound_internal (tm : NTM k) :
    (emitStepStateFormulas tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_ofFn] at hroutine
  obtain ⟨stateIndex, rfl⟩ := hroutine
  exact emitNextStateFormula_sound tm ((Fintype.equivFin tm.Q).symm stateIndex)

theorem emitStepHeadTapeFormulas_sound_internal (tm : NTM k)
    (tape : TapeSlot k) :
    (emitStepHeadTapeFormulas tm tape).Sound :=
  (emitNextHeadFormula_sound tm tape).binaryFor Work.position Work.limit₁ |>.seq
    (BinaryRoutine.clear_sound Work.position)

theorem emitStepImmutableCellPosition_sound_internal (tm : NTM k)
    (tape : TapeSlot k) :
    (emitStepImmutableCellPosition tm tape).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_ofFn] at hroutine
  obtain ⟨symbolIndex, rfl⟩ := hroutine
  exact emitNextCellCopy_sound (Fintype.card tm.Q) (k + 2) tape.index
    (CircuitUnrolling.symbolIndex (symbolEquiv.symm symbolIndex))

theorem emitStepWritableCellPosition_sound_internal (tm : NTM k)
    (tape : WritableSlot k) :
    (emitStepWritableCellPosition tm tape).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_ofFn] at hroutine
  obtain ⟨symbolIndex, rfl⟩ := hroutine
  exact
    (emitNextCellCopy_sound (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index
      (CircuitUnrolling.symbolIndex (symbolEquiv.symm symbolIndex))).branchZero
        (emitNextWrittenCellFormula_sound tm tape
          (symbolEquiv.symm symbolIndex)) Work.position

theorem emitStepCellTapeFormulas_sound_internal (tm : NTM k)
    (tape : TapeSlot k) :
    (emitStepCellTapeFormulas tm tape).Sound := by
  cases tape with
  | input =>
      exact
        (emitStepImmutableCellPosition_sound_internal tm .input).binaryFor
            Work.position Work.limit₁ |>.seq
          (BinaryRoutine.clear_sound Work.position)
  | work index =>
      exact
        (emitStepWritableCellPosition_sound_internal tm (.work index)).binaryFor
            Work.position Work.limit₁ |>.seq
          (BinaryRoutine.clear_sound Work.position)
  | output =>
      exact
        (emitStepWritableCellPosition_sound_internal tm .output).binaryFor
            Work.position Work.limit₁ |>.seq
          (BinaryRoutine.clear_sound Work.position)

theorem emitStepFormulas_sound_internal (tm : NTM k) :
    (emitStepFormulas tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hroutine
  rcases hroutine with
    ((((hstate | hlimit₁) | hhead) | hlimit₂) | hcell) | hclear
  · subst routine
    exact emitStepStateFormulas_sound_internal tm
  · subst routine
    exact setStepPositionLimit_sound_for_step 1
  · obtain ⟨tape, _htape, rfl⟩ := hhead
    exact emitStepHeadTapeFormulas_sound_internal tm tape
  · subst routine
    exact setStepPositionLimit_sound_for_step 2
  · obtain ⟨tape, _htape, rfl⟩ := hcell
    exact emitStepCellTapeFormulas_sound_internal tm tape
  · subst routine
    exact BinaryRoutine.clear_sound Work.limit₁

theorem emitStepStateCopies_sound_internal (tm : NTM k) :
    (emitStepStateCopies tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_ofFn] at hroutine
  obtain ⟨stateIndex, rfl⟩ := hroutine
  exact emitPackedFormulaCopy_sound
    (stateNextFormulaPolynomial tm ((Fintype.equivFin tm.Q).symm stateIndex))

theorem emitStepHeadTapeCopies_sound_internal (tm : NTM k)
    (tape : TapeSlot k) :
    (emitStepHeadTapeCopies tm tape).Sound :=
  (emitPackedFormulaCopy_sound (headNextFormulaPolynomial tm tape)).binaryFor
      Work.position Work.limit₁ |>.seq
    (BinaryRoutine.clear_sound Work.position)

theorem emitStepWritableCellCopies_sound_internal (tm : NTM k)
    (tape : WritableSlot k) :
    (emitStepWritableCellCopies tm tape).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_ofFn] at hroutine
  obtain ⟨symbolIndex, rfl⟩ := hroutine
  exact
    (emitPackedFormulaCopy_sound (Polynomial.C 1)).branchZero
      (emitPackedFormulaCopy_sound
        (writtenNextFormulaPolynomial tm tape (symbolEquiv.symm symbolIndex)))
      Work.position

theorem emitStepCellTapeCopies_sound_internal (tm : NTM k)
    (tape : TapeSlot k) :
    (emitStepCellTapeCopies tm tape).Sound := by
  cases tape with
  | input =>
      exact emitStepImmutableCellCopies_sound_for_step.binaryFor Work.position
        Work.limit₁ |>.seq (BinaryRoutine.clear_sound Work.position)
  | work index =>
      exact
        (emitStepWritableCellCopies_sound_internal tm (.work index)).binaryFor
            Work.position Work.limit₁ |>.seq
          (BinaryRoutine.clear_sound Work.position)
  | output =>
      exact
        (emitStepWritableCellCopies_sound_internal tm .output).binaryFor
            Work.position Work.limit₁ |>.seq
          (BinaryRoutine.clear_sound Work.position)

theorem emitStepPackedCopies_sound_internal (tm : NTM k) :
    (emitStepPackedCopies tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hroutine
  rcases hroutine with
    ((((hstate | hlimit₁) | hhead) | hlimit₂) | hcell) | hclear
  · subst routine
    exact emitStepStateCopies_sound_internal tm
  · subst routine
    exact setStepPositionLimit_sound_for_step 1
  · obtain ⟨tape, _htape, rfl⟩ := hhead
    exact emitStepHeadTapeCopies_sound_internal tm tape
  · subst routine
    exact setStepPositionLimit_sound_for_step 2
  · obtain ⟨tape, _htape, rfl⟩ := hcell
    exact emitStepCellTapeCopies_sound_internal tm tape
  · subst routine
    exact BinaryRoutine.clear_sound Work.limit₁

theorem emitStep_sound_internal (tm : TM k) :
    (emitStep tm).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with hsaveBase | hformulas | hsaveConfig | hrestoreCursor |
    hcopies | hclearBase | hclearCursor
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.available Work.gateBound
      Work.copyCounter
  · subst routine
    exact emitStepFormulas_sound_internal tm.toNTM
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.available Work.configBase
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.gateBound Work.gateCount
      Work.copyCounter
  · subst routine
    exact emitStepPackedCopies_sound_internal tm.toNTM
  · subst routine
    exact BinaryRoutine.clear_sound Work.gateBound
  · subst routine
    exact BinaryRoutine.clear_sound Work.gateCount

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
