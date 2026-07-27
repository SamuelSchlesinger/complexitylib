/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Predecessor.Internal

/-!
# Verified direct predecessor-head formula generation

This module exposes the executable predecessor-head generator together with
its exact entry domain, restored work-vector effect, and encoded numeric
schedule. Direction codes zero and one mean left and right; all other codes
mean stay, matching `movedHeadPositionCode`.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Direct predecessor-head generation is sound on its explicit clean domain. -/
theorem emitPredecessorHeadFormula_sound (stateCount directionCode : ℕ) :
    (emitPredecessorHeadFormula stateCount directionCode).Sound :=
  emitPredecessorHeadFormula_sound_internal stateCount directionCode

/-- The generator's domain is exactly clean owned scratch, a positive horizon,
and an in-range target position. -/
theorem emitPredecessorHeadFormula_requires
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount) :
    (emitPredecessorHeadFormula stateCount directionCode).requires values ↔
      PredecessorHeadClean values ∧ 0 < values Work.horizon ∧
        values Work.position ≤ values Work.horizon :=
  emitPredecessorHeadFormula_requires_internal stateCount directionCode values

/-- Complete predecessor-head emission has an all-prefix pointwise width
certificate on its natural clean domain. The frontier premise covers every
emitted wire; the single arithmetic cap covers both absolute head references
and the dynamic reverse-fold offset. -/
theorem emitPredecessorHeadFormula_spaceBoundByWidth
    (stateCount directionCode : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, PredecessorHeadClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          movedHeadPredecessorSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hcap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.horizon + 1) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 +
          2 * (values inputLength Work.horizon + 2) ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPredecessorHeadFormula stateCount directionCode) initialSpace
      values width :=
  emitPredecessorHeadFormula_spaceBoundByWidth_internal stateCount
    directionCode hclean hhorizon htarget hvalues hfrontier hcap

/-- The generator restores every owned scratch register and advances the wire
frontier by exactly the predecessor-head schedule size. -/
theorem emitPredecessorHeadFormula_effect
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadPredecessorSize (values Work.horizon)) :=
  emitPredecessorHeadFormula_effect_internal stateCount directionCode values
    hclean hhorizon htarget

/-- The emitted word is exactly the encoded numeric predecessor-head schedule
at the run-time layout, target, and horizon. -/
theorem emitPredecessorHeadFormula_emitted
    (stateCount directionCode : ℕ) (values : BinaryValues WorkCount)
    (hclean : PredecessorHeadClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon) :
    (emitPredecessorHeadFormula stateCount directionCode).emitted values =
      (predecessorHeadFormulaSchedule stateCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.position)
        directionCode).flatMap CircuitCode.RawGate.encode :=
  emitPredecessorHeadFormula_emitted_internal stateCount directionCode values
    hclean hhorizon htarget

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
