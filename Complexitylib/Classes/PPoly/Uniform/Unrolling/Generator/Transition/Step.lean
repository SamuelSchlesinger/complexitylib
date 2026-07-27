/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal

/-!
# Verified direct packed-step generation

This module exposes the complete deterministic transition-layer generator.
Its contracts cover the concrete machine, its clean entry domain, exact
register effect, restored scratch convention, and byte-for-byte emitted
packed transition fragment.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete deterministic packed-step generation is sound. -/
theorem emitStep_sound (tm : TM k) : (emitStep tm).Sound :=
  emitStep_sound_internal tm

/-- A clean work vector and positive tableau horizon satisfy the complete
step generator's explicit domain. -/
theorem emitStep_requires (tm : TM k) (values : BinaryValues WorkCount)
    (hclean : StepClean values) (hhorizon : 0 < values Work.horizon) :
    (emitStep tm).requires values :=
  emitStep_requires_internal tm values hclean hhorizon

/-- The complete step advances the wire frontier by the exact numeric
schedule size, records the packed successor base, and clears both gate
bookkeeping registers. -/
@[simp] theorem emitStep_effect (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStep tm).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.available
              (values Work.available +
                stepScheduleSize (transitionCases tm.toNTM).length
                  (Fintype.card tm.Q) k (values Work.horizon)
                  (stepAtomKindAt tm.toNTM (values Work.horizon))
                  (stepAtomEffectSelectedAt tm.toNTM (values Work.horizon))
                  (effectCaseChoiceAt tm.toNTM)))
            Work.configBase
              (stepScheduleOutputBase (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (values Work.horizon)
                (values Work.available)
                (stepAtomKindAt tm.toNTM (values Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (values Work.horizon))
                (effectCaseChoiceAt tm.toNTM)))
          Work.gateBound 0) Work.gateCount 0 :=
  emitStep_effect_canonical_internal tm values hclean hhorizon

/-- A complete step restores the reusable clean-entry convention. -/
theorem emitStep_preserves_clean (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    StepClean ((emitStep tm).effect values) :=
  emitStep_effect_stepClean_internal tm values hclean hhorizon

/-- A complete deterministic transition layer has an advertised all-prefix
auxiliary-space bound controlled by one shared numeric width envelope. -/
theorem emitStep_spaceBoundByWidth (tm : TM k)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm.toNTM (values inputLength) (width inputLength)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStep tm) initialSpace values width :=
  emitStep_spaceBoundByWidth_internal tm hclean hhorizon henvelope

/-- The emitted word is exactly the encoded canonical packed transition
fragment, with deterministic choice wire zero. -/
@[simp] theorem emitStep_emitted (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStep tm).emitted values =
      (stepFragment tm.toNTM (values Work.horizon) (values Work.configBase) 0
        (values Work.available)).flatMap CircuitCode.RawGate.encode := by
  rw [emitStep_emitted_internal tm values hclean hhorizon,
    stepFragment_eq_stepSchedule]
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  rw [hcard]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
