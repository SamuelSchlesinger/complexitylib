/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.MovedHead.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.MovedHead.Internal

/-!
# Verified direct moved-head formula generation

This module exposes the complete three-direction moved-head generator together
with its clean entry domain, restored work-vector effect, and exact encoded
numeric schedule.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete moved-head formula generation is sound. -/
theorem emitMovedHeadFormula_sound (tm : NTM k) (tape : TapeSlot k) :
    (emitMovedHeadFormula tm tape).Sound :=
  emitMovedHeadFormula_sound_internal tm tape

/-- Complete moved-head emission has an all-prefix width certificate under one
bounded-selector envelope. The full schedule covers every member frontier;
the remaining visible terms cover nested case references, predecessor-head
references and controller slack, and the conjunction's polynomial evaluator. -/
theorem emitMovedHeadFormula_spaceBoundByWidth
    (tm : NTM k) (tape : TapeSlot k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, MovedHeadFormulaClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (htarget : ∀ inputLength,
      values inputLength Work.position ≤ values inputLength Work.horizon)
    (havailable : ∀ inputLength, 1 ≤ values inputLength Work.available)
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon + 1 →
        values inputLength Work.available +
            movedHeadFormulaScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) + position) +
              (values inputLength Work.horizon + 2) + (k + 2) + tapeIndex +
              4) +
          caseReadSize (values inputLength Work.horizon) +
          2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
            (values inputLength Work.horizon) +
          2 * (values inputLength Work.horizon + 2) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitMovedHeadFormula tm tape)
      initialSpace values width :=
  emitMovedHeadFormula_spaceBoundByWidth_internal tm tape hclean hhorizon
    htarget havailable hvalues hcap

/-- Clean owned scratch, a positive horizon, an in-range target, and a valid
wire frontier suffice for complete moved-head formula generation. -/
theorem emitMovedHeadFormula_requires (tm : NTM k) (tape : TapeSlot k)
    (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).requires values :=
  emitMovedHeadFormula_requires_internal tm tape values hclean hhorizon
    htarget havailable

/-- Moved-head generation restores every owned register and advances only the
wire frontier by the exact numeric schedule size. -/
@[simp] theorem emitMovedHeadFormula_effect (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).effect values =
      Function.update values Work.available
        (values Work.available +
          movedHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) :=
  emitMovedHeadFormula_effect_internal tm tape values hclean hhorizon htarget
    havailable

/-- The emitted word is literally the canonical numeric moved-head schedule,
including all three direction members, the false identity, and reverse fold. -/
@[simp] theorem emitMovedHeadFormula_emitted (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (htarget : values Work.position ≤ values Work.horizon)
    (havailable : 1 ≤ values Work.available) :
    (emitMovedHeadFormula tm tape).emitted values =
      (movedHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.index (values Work.position)
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitMovedHeadFormula_emitted_internal tm tape values hclean hhorizon
    htarget havailable

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
