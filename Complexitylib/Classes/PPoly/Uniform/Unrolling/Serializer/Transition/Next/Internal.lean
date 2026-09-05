/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.MovedHead
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Next.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell

/-!
# Numeric next-atom schedules -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem length_nextHaltedOrSchedule_internal
    (haltWire available oldWire : ℕ) (nextSchedule : CircuitCode.RawCircuit) :
    (nextHaltedOrSchedule haltWire available oldWire nextSchedule).length =
      nextHaltedOrScheduleSize nextSchedule.length := by
  simp [nextHaltedOrSchedule, nextHaltedOrScheduleSize, haltedOrSchedule]

theorem length_nextStateFormulaSchedule_internal
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
          choiceAt := by
  simp [nextStateFormulaSchedule, nextStateFormulaScheduleSize,
    length_nextHaltedOrSchedule_internal]

theorem length_nextHeadFormulaSchedule_internal
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
          choiceAt := by
  simp [nextHeadFormulaSchedule, nextHeadFormulaScheduleSize,
    length_nextHaltedOrSchedule_internal]

theorem length_nextCellCopySchedule_internal
    (stateCount tapeCount T configBase tapeIndex position symbolIndex : ℕ) :
    (nextCellCopySchedule stateCount tapeCount T configBase tapeIndex position
      symbolIndex).length = nextCellCopyScheduleSize := by
  rfl

theorem length_nextWrittenCellFormulaSchedule_internal
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
          choiceAt := by
  simp [nextWrittenCellFormulaSchedule, nextWrittenCellFormulaScheduleSize,
    length_nextHaltedOrSchedule_internal]

theorem length_nextFormulaSchedule_internal
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
          choiceAt := by
  simp only [nextFormulaSchedule, nextFormulaScheduleSize]
  split <;> rename_i hstate
  · exact length_nextStateFormulaSchedule_internal caseCount stateCount
      workCount T configBase choiceWire available stateIndex haltStateIndex
      (selectedAt 0) choiceAt caseStateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt
  · split <;> rename_i hhead
    · exact length_nextHeadFormulaSchedule_internal caseCount stateCount
        workCount T configBase choiceWire available tapeIndex position
        haltStateIndex selectedAt choiceAt caseStateIndexAt inputSymbolIndexAt
        outputSymbolIndexAt workSymbolIndexAt
    · split <;> rename_i hwritten
      · exact length_nextWrittenCellFormulaSchedule_internal caseCount
          stateCount workCount T configBase choiceWire available tapeIndex
          position symbolIndex haltStateIndex (selectedAt 0) choiceAt
          caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt
          workSymbolIndexAt
      · exact length_nextCellCopySchedule_internal stateCount
          (workCount + 2) T configBase tapeIndex position symbolIndex

theorem compileRaw_nextStateFormula_eq_schedule_internal
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
        (effectCaseWorkSymbolIndexAt tm) := by
  unfold nextFormula
  rw [compileRaw_haltedOrFormula_eq_schedule]
  simp only [configVar, BoolFormula.size, BoolFormula.compileRaw]
  unfold selectedStateFormula
  rw [compileRaw_effectFormula_eq_schedule]
  simp [nextStateFormulaSchedule, nextHaltedOrSchedule,
    nextFormulaChildAvailable, nextHaltStateIndex, configWire]

theorem compileRaw_nextHeadFormula_eq_schedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire (.head tape target)) =
      nextHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available tape.index.val
        target.val (nextHaltStateIndex tm) (movedHeadCaseSelectedAt tm tape)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  unfold nextFormula
  rw [compileRaw_haltedOrFormula_eq_schedule]
  simp only [configVar, BoolFormula.size, BoolFormula.compileRaw]
  rw [compileRaw_movedHeadFormula_eq_schedule]
  simp [nextHeadFormulaSchedule, nextHaltedOrSchedule,
    nextFormulaChildAvailable, nextHaltStateIndex, configWire,
    transitionHeadRef]

theorem compileRaw_nextInputCellFormula_eq_schedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (position : Fin (T + 2)) (symbol : Γ) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire
          (.cell .input position symbol)) =
      nextCellCopySchedule (Fintype.card tm.Q) (k + 2) T configBase
        (TapeSlot.input : TapeSlot k).index.val position.val
        (symbolIndex symbol).val := by
  simp [nextFormula, configVar, BoolFormula.compileRaw, nextCellCopySchedule,
    configWire, transitionCellRef]

theorem compileRaw_nextWritableMarkerFormula_eq_schedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : WritableSlot k) (position : Fin (T + 2)) (symbol : Γ)
    (hposition : position.val = 0) :
    BoolFormula.compileRaw available
        (nextFormula tm T configBase choiceWire
          (.cell tape.toTapeSlot position symbol)) =
      nextCellCopySchedule (Fintype.card tm.Q) (k + 2) T configBase
        tape.toTapeSlot.index.val position.val (symbolIndex symbol).val := by
  cases tape <;>
    simp [nextFormula, hposition, configVar, BoolFormula.compileRaw,
      nextCellCopySchedule, configWire, transitionCellRef,
      WritableSlot.toTapeSlot]

theorem compileRaw_nextWrittenCellFormula_eq_schedule_internal
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
        (effectCaseWorkSymbolIndexAt tm) := by
  cases tape <;>
    simp only [WritableSlot.toTapeSlot, nextFormula, hposition, ite_false]
  all_goals rw [compileRaw_haltedOrFormula_eq_schedule]
  all_goals simp only [configVar, BoolFormula.size, BoolFormula.compileRaw]
  all_goals rw [compileRaw_writtenCellFormula_eq_schedule]
  all_goals simp [nextWrittenCellFormulaSchedule, nextHaltedOrSchedule,
    nextFormulaChildAvailable, nextHaltStateIndex, configWire,
    transitionCellRef, WritableSlot.toTapeSlot, Nat.add_assoc]

theorem compileRaw_nextFormula_eq_schedule_internal
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
        (effectCaseWorkSymbolIndexAt tm) := by
  cases atom with
  | state state =>
      simpa [nextFormulaSchedule, nextAtomKind, nextAtomStateIndex,
        nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex,
        nextAtomEffectSelectedAt, nextStateAtomKind, nextHeadAtomKind,
        nextWritableCellAtomKind] using
        compileRaw_nextStateFormula_eq_schedule_internal tm T configBase
          choiceWire available state
  | head tape target =>
      simpa [nextFormulaSchedule, nextAtomKind, nextAtomStateIndex,
        nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex,
        nextAtomEffectSelectedAt, nextStateAtomKind, nextHeadAtomKind,
        nextWritableCellAtomKind] using
        compileRaw_nextHeadFormula_eq_schedule_internal tm T configBase
          choiceWire available tape target
  | cell tape position symbol =>
      cases tape with
      | input =>
          simpa [nextFormulaSchedule, nextAtomKind, nextAtomStateIndex,
            nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex,
            nextAtomEffectSelectedAt, nextStateAtomKind, nextHeadAtomKind,
            nextInputCellAtomKind, nextWritableCellAtomKind] using
            compileRaw_nextInputCellFormula_eq_schedule_internal tm T
              configBase choiceWire available position symbol
      | work i =>
          by_cases hposition : position.val = 0
          · simpa [nextFormulaSchedule, nextAtomKind, nextAtomStateIndex,
              nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex,
              nextAtomEffectSelectedAt, nextStateAtomKind, nextHeadAtomKind,
              nextWritableMarkerAtomKind, nextWritableCellAtomKind, hposition,
              WritableSlot.toTapeSlot] using
              compileRaw_nextWritableMarkerFormula_eq_schedule_internal tm T
                configBase choiceWire available (.work i) position symbol
                hposition
          · simpa [nextFormulaSchedule, nextAtomKind, nextAtomStateIndex,
              nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex,
              nextAtomEffectSelectedAt, nextStateAtomKind, nextHeadAtomKind,
              nextWritableCellAtomKind, hposition, WritableSlot.toTapeSlot]
              using
              compileRaw_nextWrittenCellFormula_eq_schedule_internal tm T
                configBase choiceWire available (.work i) position symbol
                hposition
      | output =>
          by_cases hposition : position.val = 0
          · simpa [nextFormulaSchedule, nextAtomKind, nextAtomStateIndex,
              nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex,
              nextAtomEffectSelectedAt, nextStateAtomKind, nextHeadAtomKind,
              nextWritableMarkerAtomKind, nextWritableCellAtomKind, hposition,
              WritableSlot.toTapeSlot] using
              compileRaw_nextWritableMarkerFormula_eq_schedule_internal tm T
                configBase choiceWire available .output position symbol
                hposition
          · simpa [nextFormulaSchedule, nextAtomKind, nextAtomStateIndex,
              nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex,
              nextAtomEffectSelectedAt, nextStateAtomKind, nextHeadAtomKind,
              nextWritableCellAtomKind, hposition, WritableSlot.toTapeSlot]
              using
              compileRaw_nextWrittenCellFormula_eq_schedule_internal tm T
                configBase choiceWire available .output position symbol
                hposition

theorem size_nextFormula_eq_scheduleSize_internal
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (atom : ConfigAtom tm T) :
    (nextFormula tm T configBase choiceWire atom).size =
      nextFormulaScheduleSize (transitionCases tm).length k T
        (nextAtomKind atom) (nextAtomEffectSelectedAt tm atom)
        (effectCaseChoiceAt tm) := by
  have hlength := congrArg List.length
    (compileRaw_nextFormula_eq_schedule_internal tm T configBase choiceWire 0
      atom)
  simpa only [BoolFormula.length_compileRaw,
    length_nextFormulaSchedule_internal] using hlength

end Serializer

end CircuitUnrolling

end Complexity
