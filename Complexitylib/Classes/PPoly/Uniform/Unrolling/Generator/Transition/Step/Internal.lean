/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Effect
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Emitted
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Packed
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Requires
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Sound
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Space
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Top
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Step
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Direct-unrolling packed-step generator -- proof internals
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem setStepPositionLimit_sound_internal (extra : ℕ) :
    (setStepPositionLimit extra).Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.limit₁
    Work.copyCounter).seq (BinaryRoutine.addConst_sound Work.limit₁ extra)

theorem setStepPositionLimit_requires_internal (extra : ℕ)
    (values : BinaryValues WorkCount)
  (hcopy : values Work.copyCounter = 0) :
    (setStepPositionLimit extra).requires values := by
  simp [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, Work.horizon, Work.limit₁, Work.copyCounter]
  simpa [Work.copyCounter] using hcopy

@[simp] theorem setStepPositionLimit_effect_internal (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (setStepPositionLimit extra).effect values =
      Function.update values Work.limit₁
        (values Work.horizon + extra) := by
  simp [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst]

@[simp] theorem setStepPositionLimit_emitted_internal (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (setStepPositionLimit extra).emitted values = [] := by
  rfl

theorem emitStepImmutableCellCopies_sound_internal :
    emitStepImmutableCellCopies.Sound :=
  BinaryRoutine.repeatRoutine_sound 4
    (emitPackedFormulaCopy (Polynomial.C 1))
    (emitPackedFormulaCopy_sound (Polynomial.C 1))

theorem emitStepImmutableCellCopies_requires_internal
    (values : BinaryValues WorkCount)
    (htemporary₃ : values Work.temporary₃ = 0)
    (hscratch : values Work.polynomialScratch = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    emitStepImmutableCellCopies.requires values := by
  have htemporary₃' : values 25 = 0 := by
    simpa [Work.temporary₃] using htemporary₃
  have hscratch' : values 11 = 0 := by
    simpa [Work.polynomialScratch] using hscratch
  have hmultiply' : values 12 = 0 := by
    simpa [Work.multiplyCounter] using hmultiply
  have hadd' : values 13 = 0 := by
    simpa [Work.addCounter] using hadd
  have hcopy' : values 10 = 0 := by
    simpa [Work.copyCounter] using hcopy
  have hemit' : values 9 = 0 := by
    simpa [Work.emitCounter] using hemit
  simp [emitStepImmutableCellCopies, BinaryRoutine.repeatRoutine,
    BinaryRoutine.seqList, BinaryRoutine.seq, emitPackedFormulaCopy_requires,
    emitPackedFormulaCopy_effect, BinaryRoutine.identity,
    BinaryRoutine.emitBits, htemporary₃', hscratch', hmultiply', hadd', hcopy',
    hemit', Work.gateCount, Work.available, Work.reference₀,
    Work.temporary₃, Work.polynomialScratch, Work.multiplyCounter,
    Work.addCounter, Work.copyCounter, Work.emitCounter]

theorem StepClean.caseFormulaClean_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values) :
    CaseFormulaClean values := by
  have hupdate : Function.update values Work.position 0 = values := by
    funext i
    by_cases hi : i = Work.position
    · subst i
      simp [hclean.position]
    · simp [hi]
  simpa [hupdate] using hclean.movedHeadClean.caseClean

theorem StepClean.writtenCellFormulaClean_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values) :
    WrittenCellFormulaClean values :=
  { caseClean := hclean.movedHeadClean.caseClean
    limit₂ := hclean.movedHeadClean.limit₂
    savedOutput := hclean.movedHeadClean.savedOutput }

theorem StepClean.movedHeadClean_atPosition_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values)
    (position : ℕ) :
    MovedHeadFormulaClean
      (Function.update values Work.position position) := by
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · have hupdate :
        Function.update (Function.update values Work.position position)
            Work.position 0 =
          Function.update values Work.position 0 := by
      funext i
      by_cases hi : i = Work.position <;> simp [hi]
    simpa [hupdate] using hclean.movedHeadClean.caseClean
  · simpa [Work.position, Work.limit₂] using hclean.movedHeadClean.limit₂
  · simpa [Work.position, Work.loop₁] using hclean.movedHeadClean.loop₁
  · simpa [Work.position, Work.savedOutput] using
      hclean.movedHeadClean.savedOutput
  · simpa [Work.position, Work.direction] using
      hclean.movedHeadClean.direction
  · simpa [Work.position, Work.atomKind] using
      hclean.movedHeadClean.atomKind

theorem StepClean.writtenCellClean_atPosition_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values)
    (position : ℕ) :
    WrittenCellFormulaClean
      (Function.update values Work.position position) := by
  let hmoved := hclean.movedHeadClean_atPosition_internal position
  exact
    { caseClean := hmoved.caseClean
      limit₂ := hmoved.limit₂
      savedOutput := hmoved.savedOutput }

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
