/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.WrittenCell.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.WrittenCell.Internal

/-!
# Verified direct written-cell formula generation

This module exposes the complete positive-cell formula generator together with
its clean entry domain, restored work-vector effect, and exact encoded numeric
schedule.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Complete written-cell formula generation is sound. -/
theorem emitWrittenCellFormula_sound (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) :
    (emitWrittenCellFormula tm tape symbol).Sound :=
  emitWrittenCellFormula_sound_internal tm tape symbol

/-- Complete written-cell emission has an all-prefix width certificate under
one global bounded-selector envelope. The cap covers the complete wire
frontier together with every state, head, cell, and read-size intermediate
used by the nested effect and fixed wrapper phases. -/
theorem emitWrittenCellFormula_spaceBoundByWidth
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      WrittenCellFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon + 1 →
        values inputLength Work.available +
            writtenCellScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (writtenCellEffectSelectedAt tm tape symbol)
              (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase)
            stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitWrittenCellFormula tm tape symbol) initialSpace values width :=
  emitWrittenCellFormula_spaceBoundByWidth_internal tm tape symbol hclean
    hvalues hposition hcap

/-- Clean owned scratch and an in-range positive-cell position suffice for
complete written-cell formula generation. -/
theorem emitWrittenCellFormula_requires (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellFormula tm tape symbol).requires values :=
  emitWrittenCellFormula_requires_internal tm tape symbol values hclean
    hposition

/-- Written-cell generation restores every owned register and advances only
the wire frontier by the exact numeric schedule size. -/
@[simp] theorem emitWrittenCellFormula_effect (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    (emitWrittenCellFormula tm tape symbol).effect values =
      Function.update values Work.available
        (values Work.available +
          writtenCellScheduleSize (transitionCases tm).length k
            (values Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm)) :=
  emitWrittenCellFormula_effect_internal tm tape symbol values hclean

/-- The emitted word is literally the canonical numeric written-cell schedule,
including both head tests, the selected-write effect, and the preservation
branch. -/
@[simp] theorem emitWrittenCellFormula_emitted (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellFormula tm tape symbol).emitted values =
      (writtenCellSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.toTapeSlot.index.val
        (values Work.position) (CircuitUnrolling.symbolIndex symbol).val
        (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode :=
  emitWrittenCellFormula_emitted_internal tm tape symbol values hclean
    hposition

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
