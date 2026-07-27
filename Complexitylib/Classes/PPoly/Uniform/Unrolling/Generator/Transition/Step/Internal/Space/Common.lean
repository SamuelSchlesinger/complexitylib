/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Emitted
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Common packed-step width helpers

This module supplies the shared list-trajectory and position-limit certificates
used to assemble the auxiliary-space proof for direct packed-step generation.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- The complete step schedule is the formula frontier followed by one packed
copy for every configuration atom. -/
theorem stepScheduleSize_eq_formulas_add_atoms_internal (tm : NTM k)
    (T : ℕ) :
    stepScheduleSize (transitionCases tm).length (Fintype.card tm.Q) k T
        (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) =
      stepFormulasEffectSizeInternal tm T +
        stepAtomCount (Fintype.card tm.Q) k T := by
  unfold stepScheduleSize
  rw [stepFormulasEffectSize_eq_prefixSize_internal]
  rfl

theorem StepWidthEnvelope.formulaFrontier_le_internal
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) :
    values Work.available +
        stepFormulasEffectSizeInternal tm (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap tm.qstart .input .output .zero 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  rw [stepScheduleSize_eq_formulas_add_atoms_internal] at hcap
  omega

theorem StepWidthEnvelope.finalFrontier_le_internal
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) :
    values Work.available + stepFormulasEffectSizeInternal tm
          (values Work.horizon) +
        stepAtomCount (Fintype.card tm.Q) k (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap tm.qstart .input .output .zero 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  rw [stepScheduleSize_eq_formulas_add_atoms_internal] at hcap
  omega

theorem StepWidthEnvelope.horizon_add_two_le_internal
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) :
    values Work.horizon + 2 ≤ width := by
  have hcap := henvelope.cap tm.qstart .input .output .zero 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  omega

theorem StepWidthEnvelope.formulaPrefix_le_internal
    {tm : NTM k} {values : BinaryValues WorkCount} {width count : ℕ}
    (henvelope : StepWidthEnvelope tm values width)
    (hcount : count ≤ stepAtomCount (Fintype.card tm.Q) k
      (values Work.horizon)) :
    values Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values Work.horizon)) count ≤ width := by
  have hfrontier := henvelope.formulaFrontier_le_internal
  rw [stepFormulasEffectSize_eq_prefixSize_internal] at hfrontier
  have hprefix := prefixSize_mono
    (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)) hcount
  omega

/-- A finite family of routines has a sequential width certificate when each
routine is certified along an explicit trajectory and its effect advances that
trajectory by one step. -/
theorem seqList_ofFn_spaceBoundByWidthAt_internal
    (count : ℕ) (routineAt : Fin count → BinaryRoutine n)
    (trajectory : ℕ → ℕ → BinaryValues n)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues n}
    {width : ℕ → ℕ}
    (hzero : trajectory 0 = values)
    (hspace : ∀ index : Fin count,
      BinaryRoutine.SpaceBoundByWidthAt (routineAt index) initialSpace
        (trajectory index.val) width)
    (hstep : ∀ index : Fin count, ∀ inputLength,
      (routineAt index).effect (trajectory index.val inputLength) =
        trajectory (index.val + 1) inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      (List.ofFn routineAt) initialSpace values width := by
  induction count generalizing values trajectory with
  | zero =>
      simp only [List.ofFn_zero, BinaryRoutine.SeqListSpaceBoundByWidthAt]
  | succ count ih =>
      rw [List.ofFn_succ]
      simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
      constructor
      · simpa [hzero] using hspace (0 : Fin (count + 1))
      · apply ih (fun index => routineAt index.succ)
          (fun index inputLength => trajectory (index + 1) inputLength)
        · funext inputLength
          have hstepZero := hstep (0 : Fin (count + 1)) inputLength
          simpa [hzero] using hstepZero.symm
        · intro index
          simpa using hspace index.succ
        · intro index inputLength
          simpa [Nat.add_assoc] using hstep index.succ inputLength

/-- Replacing the outer position limit by `horizon + extra` preserves a common
width bound when the input vector and the replacement value fit that width. -/
theorem setStepPositionLimit_spaceBoundByWidthAt_internal
    (extra : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hresult : ∀ inputLength,
      values inputLength Work.horizon + extra ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (setStepPositionLimit extra)
      initialSpace values width := by
  rw [setStepPositionLimit]
  apply BinaryRoutine.SpaceBoundByWidthAt.seq
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · exact fun inputLength => hvalues inputLength Work.horizon
    · exact fun inputLength => hvalues inputLength Work.limit₁
  · apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro inputLength
    simpa [BinaryRoutine.binaryCopy, Work.horizon, Work.limit₁] using
      hresult inputLength

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
