/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Next.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Next.Internal

/-!
# Numeric schedules for next-configuration atoms

This module exposes a common natural-number interface for the five branches
of `nextFormula`: state, head, immutable input cell, immutable writable marker,
and positive writable cell. Each nontrivial branch reuses the corresponding
public transition schedule.

## Main results

- The branch length theorems give exact numeric gate counts.
- `length_nextFormulaSchedule` gives the exact count selected by an atom kind.
- The branch compilation theorems expose each literal schedule adapter.
- `compileRaw_nextFormula_eq_schedule` proves the common literal adapter.
- `size_nextFormula_eq_scheduleSize` identifies the formula size with that
  common numeric count.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- A one-gate old atom plus the halted-or wrapper contributes seven gates
beyond the next-value child. -/
@[simp] theorem length_nextHaltedOrSchedule
    (haltWire available oldWire : ℕ) (nextSchedule : CircuitCode.RawCircuit) :
    (nextHaltedOrSchedule haltWire available oldWire nextSchedule).length =
      nextHaltedOrScheduleSize nextSchedule.length :=
  length_nextHaltedOrSchedule_internal haltWire available oldWire nextSchedule

/-- Exact gate count of a state-atom schedule. -/
@[simp] theorem length_nextStateFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available
      stateIndex haltStateIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (nextStateFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available stateIndex haltStateIndex selectedAt choiceAt
      caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt
      workSymbolIndexAt).length =
        nextStateFormulaScheduleSize caseCount workCount T selectedAt
          choiceAt :=
  length_nextStateFormulaSchedule_internal caseCount stateCount workCount T
    configBase choiceWire available stateIndex haltStateIndex selectedAt
    choiceAt caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt

/-- Exact gate count of a head-atom schedule. -/
@[simp] theorem length_nextHeadFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      target haltStateIndex : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (nextHeadFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target haltStateIndex selectedAt choiceAt
      caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt
      workSymbolIndexAt).length =
        nextHeadFormulaScheduleSize caseCount workCount T selectedAt
          choiceAt :=
  length_nextHeadFormulaSchedule_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex target haltStateIndex selectedAt
    choiceAt caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt

/-- Immutable input and writable marker cells emit one copy gate. -/
@[simp] theorem length_nextCellCopySchedule
    (stateCount tapeCount T configBase tapeIndex position symbolIndex : ℕ) :
    (nextCellCopySchedule stateCount tapeCount T configBase tapeIndex position
      symbolIndex).length = nextCellCopyScheduleSize :=
  length_nextCellCopySchedule_internal stateCount tapeCount T configBase
    tapeIndex position symbolIndex

/-- Exact gate count of a positive writable-cell schedule. -/
@[simp] theorem length_nextWrittenCellFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex haltStateIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (nextWrittenCellFormulaSchedule caseCount stateCount workCount T
      configBase choiceWire available tapeIndex position symbolIndex
      haltStateIndex selectedAt choiceAt caseStateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt).length =
        nextWrittenCellFormulaScheduleSize caseCount workCount T selectedAt
          choiceAt :=
  length_nextWrittenCellFormulaSchedule_internal caseCount stateCount
    workCount T configBase choiceWire available tapeIndex position symbolIndex
    haltStateIndex selectedAt choiceAt caseStateIndexAt inputSymbolIndexAt
    outputSymbolIndexAt workSymbolIndexAt

/-- Exact gate count selected by the common numeric atom-kind interface. -/
@[simp] theorem length_nextFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available atomKind
      stateIndex tapeIndex position symbolIndex haltStateIndex : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (nextFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available atomKind stateIndex tapeIndex position symbolIndex
      haltStateIndex selectedAt choiceAt caseStateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt).length =
        nextFormulaScheduleSize caseCount workCount T atomKind selectedAt
          choiceAt :=
  length_nextFormulaSchedule_internal caseCount stateCount workCount T
    configBase choiceWire available atomKind stateIndex tapeIndex position
    symbolIndex haltStateIndex selectedAt choiceAt caseStateIndexAt
    inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- Literal raw schedule for the state branch of `nextFormula`. -/
theorem compileRaw_nextStateFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (state : tm.Q) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire (.state state)) =
      nextStateFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available
        (stateIndex tm state) (nextHaltStateIndex tm)
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState = state))
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) :=
  compileRaw_nextStateFormula_eq_schedule_internal tm T configBase choiceWire
    available state

/-- Literal raw schedule for the head branch of `nextFormula`. -/
theorem compileRaw_nextHeadFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire (.head tape target)) =
      nextHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available tape.index.val
        target.val (nextHaltStateIndex tm) (movedHeadCaseSelectedAt tm tape)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) :=
  compileRaw_nextHeadFormula_eq_schedule_internal tm T configBase choiceWire
    available tape target

/-- Literal one-gate raw schedule for an immutable input-cell atom. -/
theorem compileRaw_nextInputCellFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (position : Fin (T + 2)) (symbol : Γ) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire
          (.cell .input position symbol)) =
      nextCellCopySchedule (Fintype.card tm.Q) (k + 2) T configBase
        (TapeSlot.input : TapeSlot k).index.val position.val
        (symbolIndex symbol).val :=
  compileRaw_nextInputCellFormula_eq_schedule_internal tm T configBase
    choiceWire available position symbol

/-- Literal one-gate raw schedule for an immutable writable marker cell. -/
theorem compileRaw_nextWritableMarkerFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : WritableSlot k) (position : Fin (T + 2)) (symbol : Γ)
    (hposition : position.val = 0) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire
          (.cell tape.toTapeSlot position symbol)) =
      nextCellCopySchedule (Fintype.card tm.Q) (k + 2) T configBase
        tape.toTapeSlot.index.val position.val (symbolIndex symbol).val :=
  compileRaw_nextWritableMarkerFormula_eq_schedule_internal tm T configBase
    choiceWire available tape position symbol hposition

/-- Literal raw schedule for a positive writable-cell atom. -/
theorem compileRaw_nextWrittenCellFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : WritableSlot k) (position : Fin (T + 2)) (symbol : Γ)
    (hposition : position.val ≠ 0) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire
          (.cell tape.toTapeSlot position symbol)) =
      nextWrittenCellFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available
        tape.toTapeSlot.index.val position.val (symbolIndex symbol).val
        (nextHaltStateIndex tm) (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) :=
  compileRaw_nextWrittenCellFormula_eq_schedule_internal tm T configBase
    choiceWire available tape position symbol hposition

/-- Exact raw compilation order selected through the common numeric atom
interface. Machine and atom data occur only in compile-time extractors; every
argument of `nextFormulaSchedule` is natural-number or Boolean data. -/
theorem compileRaw_nextFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (atom : ConfigAtom tm T) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire atom) =
      nextFormulaSchedule (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available (nextAtomKind atom)
        (nextAtomStateIndex tm atom) (nextAtomTapeIndex atom)
        (nextAtomPosition atom) (nextAtomSymbolIndex atom)
        (nextHaltStateIndex tm) (nextAtomEffectSelectedAt tm atom)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) :=
  compileRaw_nextFormula_eq_schedule_internal tm T configBase choiceWire
    available atom

/-- The syntax-tree size of every next atom equals its selected numeric
schedule count. -/
theorem size_nextFormula_eq_scheduleSize
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (atom : ConfigAtom tm T) :
    (nextFormula tm T configBase choiceWire atom).size =
      nextFormulaScheduleSize (transitionCases tm).length k T
        (nextAtomKind atom) (nextAtomEffectSelectedAt tm atom)
        (effectCaseChoiceAt tm) :=
  size_nextFormula_eq_scheduleSize_internal tm T configBase choiceWire atom

end Serializer

end CircuitUnrolling

end Complexity
