/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case.Internal

/-!
# Numeric transition-case schedules

This module exposes the exact natural-index schedule for one fixed local
transition case. Its run-time parameters are natural numbers and one Boolean
choice value; machine states, tape slots, symbols, and formula syntax occur
only in the final compilation adapter.

## Main results

- `length_caseFormulaSchedule` gives the exact gate count.
- The `getElem_caseFormulaSchedule_*` theorems identify every numeric phase.
- `compileRaw_caseFormula_eq_schedule` identifies the complete raw stream.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

@[simp] theorem length_caseChoiceLiteralSchedule
    (available choiceWire : ℕ) (choiceValue : Bool) :
    (caseChoiceLiteralSchedule available choiceWire choiceValue).length =
      caseChoiceLiteralSize choiceValue :=
  length_caseChoiceLiteralSchedule_internal available choiceWire choiceValue

@[simp] theorem length_caseWorkReadGates
    (stateCount workCount T configBase available : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseWorkReadGates stateCount workCount T configBase available choiceValue
      workSymbolAt).length = workCount * caseReadSize T :=
  length_caseWorkReadGates_internal stateCount workCount T configBase
    available choiceValue workSymbolAt

theorem getElem_caseWorkReadGates
    (stateCount workCount T configBase available : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (workIndex : Fin workCount) (offset : Fin (caseReadSize T)) :
    (caseWorkReadGates stateCount workCount T configBase available choiceValue
      workSymbolAt)[workIndex.val * caseReadSize T + offset.val]'(by
        rw [length_caseWorkReadGates]
        nlinarith [workIndex.isLt, offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseWorkReadAvailable T available workIndex.val choiceValue)
        (workIndex.val + 1) (workSymbolAt workIndex.val))[offset.val]'(by
          rw [length_readFormulaSchedule]
          exact offset.isLt) :=
  getElem_caseWorkReadGates_internal stateCount workCount T configBase
    available choiceValue workSymbolAt workIndex offset

@[simp] theorem length_caseFormulaMemberGates
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaMemberGates stateCount workCount T configBase choiceWire
      available stateIndex inputSymbolIndex outputSymbolIndex choiceValue
      workSymbolAt).length =
        caseFormulaMembersSize workCount T choiceValue :=
  length_caseFormulaMemberGates_internal stateCount workCount T configBase
    choiceWire available stateIndex inputSymbolIndex outputSymbolIndex
    choiceValue workSymbolAt

@[simp] theorem length_caseFormulaSchedule
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue
      workSymbolAt).length =
        caseFormulaScheduleSize workCount T choiceValue :=
  length_caseFormulaSchedule_internal stateCount workCount T configBase
    choiceWire available stateIndex inputSymbolIndex outputSymbolIndex
    choiceValue workSymbolAt

theorem getElem_caseFormulaSchedule_choice
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (offset : Fin (caseChoiceLiteralSize choiceValue)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        offset.val]'(by
          rw [length_caseFormulaSchedule]
          simp [caseFormulaScheduleSize, caseFormulaMembersSize,
            caseFormulaMemberCount]
          nlinarith [offset.isLt]) =
      (caseChoiceLiteralSchedule available choiceWire choiceValue)[offset.val]'(by
        rw [length_caseChoiceLiteralSchedule]
        exact offset.isLt) :=
  getElem_caseFormulaSchedule_choice_internal stateCount workCount T configBase
    choiceWire available stateIndex inputSymbolIndex outputSymbolIndex
    choiceValue workSymbolAt offset

theorem getElem_caseFormulaSchedule_state
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue]'(by
          rw [length_caseFormulaSchedule]
          simp [caseFormulaScheduleSize, caseFormulaMembersSize,
            caseFormulaMemberCount]
          omega) =
      CircuitCode.RawGate.copy (transitionStateRef configBase stateIndex) :=
  getElem_caseFormulaSchedule_state_internal stateCount workCount T configBase
    choiceWire available stateIndex inputSymbolIndex outputSymbolIndex
    choiceValue workSymbolAt

theorem getElem_caseFormulaSchedule_inputRead
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (offset : Fin (caseReadSize T)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue + 1 + offset.val]'(by
          rw [length_caseFormulaSchedule]
          simp [caseFormulaScheduleSize, caseFormulaMembersSize,
            caseFormulaMemberCount]
          nlinarith [offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseInputReadAvailable available choiceValue) 0 inputSymbolIndex)[
          offset.val]'(by
            rw [length_readFormulaSchedule]
            exact offset.isLt) :=
  getElem_caseFormulaSchedule_inputRead_internal stateCount workCount T
    configBase choiceWire available stateIndex inputSymbolIndex
    outputSymbolIndex choiceValue workSymbolAt offset

theorem getElem_caseFormulaSchedule_workRead
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (workIndex : Fin workCount) (offset : Fin (caseReadSize T)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue + 1 + caseReadSize T +
          workIndex.val * caseReadSize T + offset.val]'(by
            rw [length_caseFormulaSchedule]
            simp [caseFormulaScheduleSize, caseFormulaMembersSize,
              caseFormulaMemberCount]
            nlinarith [workIndex.isLt, offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseWorkReadAvailable T available workIndex.val choiceValue)
        (workIndex.val + 1) (workSymbolAt workIndex.val))[offset.val]'(by
          rw [length_readFormulaSchedule]
          exact offset.isLt) :=
  getElem_caseFormulaSchedule_workRead_internal stateCount workCount T
    configBase choiceWire available stateIndex inputSymbolIndex
    outputSymbolIndex choiceValue workSymbolAt workIndex offset

theorem getElem_caseFormulaSchedule_outputRead
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (offset : Fin (caseReadSize T)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue + 1 +
          (workCount + 1) * caseReadSize T + offset.val]'(by
            rw [length_caseFormulaSchedule]
            simp [caseFormulaScheduleSize, caseFormulaMembersSize,
              caseFormulaMemberCount]
            nlinarith [offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseOutputReadAvailable workCount T available choiceValue)
        (workCount + 1) outputSymbolIndex)[offset.val]'(by
          rw [length_readFormulaSchedule]
          exact offset.isLt) :=
  getElem_caseFormulaSchedule_outputRead_internal stateCount workCount T
    configBase choiceWire available stateIndex inputSymbolIndex
    outputSymbolIndex choiceValue workSymbolAt offset

theorem getElem_caseFormulaSchedule_identity
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseFormulaMembersSize workCount T choiceValue]'(by
          rw [length_caseFormulaSchedule]
          simp [caseFormulaScheduleSize, caseFormulaMemberCount]
          omega) = CircuitCode.RawGate.constant 0 true :=
  getElem_caseFormulaSchedule_identity_internal stateCount workCount T
    configBase choiceWire available stateIndex inputSymbolIndex
    outputSymbolIndex choiceValue workSymbolAt

theorem getElem_caseFormulaSchedule_connector
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (rank : Fin (caseFormulaMemberCount workCount)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseFormulaMembersSize workCount T choiceValue + 1 + rank.val]'(by
          rw [length_caseFormulaSchedule]
          simp [caseFormulaScheduleSize]) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) rank.val :=
  getElem_caseFormulaSchedule_connector_internal stateCount workCount T
    configBase choiceWire available stateIndex inputSymbolIndex
    outputSymbolIndex choiceValue workSymbolAt rank

/-- Exact raw compilation order of one fixed local transition case. -/
theorem compileRaw_caseFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (view : TransitionCase tm) :
    BoolFormula.compileRaw available
        (caseFormula tm T configBase choiceWire view) =
      caseFormulaSchedule (Fintype.card tm.Q) k T configBase choiceWire
        available (stateIndex tm view.state) (symbolIndex view.inputRead).val
        (symbolIndex view.outputRead).val view.choice
        (fun index => if hindex : index < k then
          (symbolIndex (view.workRead ⟨index, hindex⟩)).val else 0) :=
  compileRaw_caseFormula_eq_schedule_internal tm T configBase choiceWire
    available view

end Serializer

end CircuitUnrolling

end Complexity
