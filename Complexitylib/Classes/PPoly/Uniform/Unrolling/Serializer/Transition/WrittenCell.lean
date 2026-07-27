/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell.Internal

/-!
# Numeric schedules for written-cell formulas

This module exposes the numeric schedule for `writtenCellFormula`. One
head-at-cell gate precedes the reused transition-effect schedule, and a fixed
six-gate suffix combines the selected write with the old cell value.

## Main results

- `length_writtenCellSchedule` gives the exact gate count.
- `getElem_writtenCellSchedule_head`, `getElem_writtenCellSchedule_effect`, and
  `getElem_writtenCellSchedule_suffix` identify the three schedule phases.
- `compileRaw_writtenCellFormula_eq_schedule` proves literal raw-list equality.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- The fixed suffix contains exactly six gates. -/
@[simp] theorem length_writtenCellSuffixGates
    (stateCount tapeCount T configBase available tapeIndex position symbolIndex
      effectSize : ℕ) :
    (writtenCellSuffixGates stateCount tapeCount T configBase available
      tapeIndex position symbolIndex effectSize).length = 6 :=
  length_writtenCellSuffixGates_internal stateCount tapeCount T configBase
    available tapeIndex position symbolIndex effectSize

/-- A bounded natural phase selects the corresponding fixed suffix gate. -/
theorem getElem_writtenCellSuffixGates
    (stateCount tapeCount T configBase available tapeIndex position symbolIndex
      effectSize : ℕ) (phase : Fin 6) :
    (writtenCellSuffixGates stateCount tapeCount T configBase available
      tapeIndex position symbolIndex effectSize)[phase.val]'(by
        rw [length_writtenCellSuffixGates]
        exact phase.isLt) =
      writtenCellSuffixGate stateCount tapeCount T configBase available
        tapeIndex position symbolIndex effectSize phase.val :=
  getElem_writtenCellSuffixGates_internal stateCount tapeCount T configBase
    available tapeIndex position symbolIndex effectSize phase

/-- The complete written-cell schedule has the advertised numeric size. -/
@[simp] theorem length_writtenCellSchedule
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
      workSymbolIndexAt).length =
        writtenCellScheduleSize caseCount workCount T selectedAt choiceAt :=
  length_writtenCellSchedule_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex position symbolIndex selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt

/-- Phase zero is the initial head-at-cell test. -/
theorem getElem_writtenCellSchedule_head
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        0]'(by
          rw [length_writtenCellSchedule]
          simp [writtenCellScheduleSize]) =
      headAtCellFormulaGate stateCount T configBase tapeIndex position :=
  getElem_writtenCellSchedule_head_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex position symbolIndex selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt

/-- The block after the head test is exactly the reused effect schedule. -/
theorem getElem_writtenCellSchedule_effect
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ)
    (offset : Fin (writtenCellEffectSize caseCount workCount T selectedAt
      choiceAt)) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        offset.val + 1]'(by
          rw [length_writtenCellSchedule]
          simp [writtenCellScheduleSize]
          omega) =
      (effectFormulaSchedule caseCount stateCount workCount T configBase
        choiceWire (available + 1) selectedAt choiceAt stateIndexAt
        inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[offset.val]'(by
          rw [length_effectFormulaSchedule]
          exact offset.isLt) :=
  getElem_writtenCellSchedule_effect_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex position symbolIndex selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt offset

/-- The final six entries are selected by an increasing natural phase code. -/
theorem getElem_writtenCellSchedule_suffix
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (phase : Fin 6) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        writtenCellEffectSize caseCount workCount T selectedAt choiceAt + 1 +
          phase.val]'(by
            rw [length_writtenCellSchedule]
            simp [writtenCellScheduleSize]
            omega) =
      writtenCellSuffixGate stateCount (workCount + 2) T configBase available
        tapeIndex position symbolIndex
        (writtenCellEffectSize caseCount workCount T selectedAt choiceAt)
        phase.val :=
  getElem_writtenCellSchedule_suffix_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex position symbolIndex selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt phase

/-- Exact raw compilation order of a written-cell formula. The dynamic
schedule inputs are natural numbers or Booleans; `tm`, `tape`, and `symbol`
determine only the fixed selection oracle. -/
theorem compileRaw_writtenCellFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : WritableSlot k) (position : Fin (T + 2)) (symbol : Γ) :
    BoolFormula.compileRaw available
        (writtenCellFormula tm T configBase choiceWire tape position symbol) =
      writtenCellSchedule (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available tape.toTapeSlot.index.val position.val
        (symbolIndex symbol).val (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) :=
  compileRaw_writtenCellFormula_eq_schedule_internal tm T configBase
    choiceWire available tape position symbol

end Serializer

end CircuitUnrolling

end Complexity
