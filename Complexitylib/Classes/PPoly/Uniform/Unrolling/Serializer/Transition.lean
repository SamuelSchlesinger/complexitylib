/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Internal

/-!
# Numeric transition-formula schedules

This module exposes natural-index schedules for the two horizon-length folds
inside tableau transition formulas. Read members occupy three gates and
predecessor-head members occupy one; both finish with a false identity gate
and reverse disjunction connectors. Formula syntax appears only in the final
proof adapters.

## Main results

- `compileRaw_readFormula_eq_schedule` identifies every read-formula stream.
- `compileRaw_predecessorHeadFormula_eq_schedule` identifies every predecessor
  head stream.
- The length and `getElem` theorems expose their exact numeric phases.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

@[simp] theorem fixedWidthSizeAt_of_lt
    {count width index : ℕ} (hindex : index < count) :
    fixedWidthSizeAt count width index = width :=
  fixedWidthSizeAt_of_lt_internal hindex

@[simp] theorem fixedWidthSizeAt_of_ge
    {count width index : ℕ} (hindex : count ≤ index) :
    fixedWidthSizeAt count width index = 0 :=
  fixedWidthSizeAt_of_ge_internal hindex

@[simp] theorem length_readFormulaMemberBlock
    (stateCount tapeCount T configBase available tapeIndex symbolIndex
      position : ℕ) :
    (readFormulaMemberBlock stateCount tapeCount T configBase available
      tapeIndex symbolIndex position).length = 3 :=
  length_readFormulaMemberBlock_internal stateCount tapeCount T configBase
    available tapeIndex symbolIndex position

@[simp] theorem length_readFormulaMemberGates
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    (readFormulaMemberGates stateCount tapeCount T configBase available
      tapeIndex symbolIndex).length = 3 * (T + 1) :=
  length_readFormulaMemberGates_internal stateCount tapeCount T configBase
    available tapeIndex symbolIndex

theorem getElem_readFormulaMemberGates
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ)
    (position : Fin (T + 1)) (offset : Fin 3) :
    (readFormulaMemberGates stateCount tapeCount T configBase available
      tapeIndex symbolIndex)[position.val * 3 + offset.val]'(by
        rw [length_readFormulaMemberGates]
        nlinarith [position.isLt, offset.isLt]) =
      (readFormulaMemberBlock stateCount tapeCount T configBase available
        tapeIndex symbolIndex position.val)[offset.val]'(by
          rw [length_readFormulaMemberBlock]
          exact offset.isLt) :=
  getElem_readFormulaMemberGates_internal stateCount tapeCount T configBase
    available tapeIndex symbolIndex position offset

@[simp] theorem length_readFormulaSchedule
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    (readFormulaSchedule stateCount tapeCount T configBase available
      tapeIndex symbolIndex).length = 4 * (T + 1) + 1 :=
  length_readFormulaSchedule_internal stateCount tapeCount T configBase
    available tapeIndex symbolIndex

theorem getElem_readFormulaSchedule_identity
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    (readFormulaSchedule stateCount tapeCount T configBase available
      tapeIndex symbolIndex)[3 * (T + 1)]'(by
        rw [length_readFormulaSchedule]
        omega) = CircuitCode.RawGate.constant 0 false :=
  getElem_readFormulaSchedule_identity_internal stateCount tapeCount T
    configBase available tapeIndex symbolIndex

theorem getElem_readFormulaSchedule_connector
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ)
    (rank : Fin (T + 1)) :
    (readFormulaSchedule stateCount tapeCount T configBase available
      tapeIndex symbolIndex)[3 * (T + 1) + 1 + rank.val]'(by
        rw [length_readFormulaSchedule]
        omega) =
      indexedRightFoldConnector .or available (T + 1)
        (fixedWidthSizeAt (T + 1) 3) rank.val :=
  getElem_readFormulaSchedule_connector_internal stateCount tapeCount T
    configBase available tapeIndex symbolIndex rank

@[simp] theorem length_predecessorHeadMemberGates
    (stateCount T configBase tapeIndex target directionCode : ℕ) :
    (predecessorHeadMemberGates stateCount T configBase tapeIndex target
      directionCode).length = T + 1 :=
  length_predecessorHeadMemberGates_internal stateCount T configBase tapeIndex
    target directionCode

@[simp] theorem length_predecessorHeadFormulaSchedule
    (stateCount T configBase available tapeIndex target directionCode : ℕ) :
    (predecessorHeadFormulaSchedule stateCount T configBase available
      tapeIndex target directionCode).length = 2 * (T + 1) + 1 :=
  length_predecessorHeadFormulaSchedule_internal stateCount T configBase
    available tapeIndex target directionCode

theorem getElem_predecessorHeadFormulaSchedule_identity
    (stateCount T configBase available tapeIndex target directionCode : ℕ) :
    (predecessorHeadFormulaSchedule stateCount T configBase available
      tapeIndex target directionCode)[T + 1]'(by
        rw [length_predecessorHeadFormulaSchedule]
        omega) = CircuitCode.RawGate.constant 0 false :=
  getElem_predecessorHeadFormulaSchedule_identity_internal stateCount T
    configBase available tapeIndex target directionCode

theorem getElem_predecessorHeadFormulaSchedule_connector
    (stateCount T configBase available tapeIndex target directionCode : ℕ)
    (rank : Fin (T + 1)) :
    (predecessorHeadFormulaSchedule stateCount T configBase available
      tapeIndex target directionCode)[T + 1 + 1 + rank.val]'(by
        rw [length_predecessorHeadFormulaSchedule]
        omega) =
      indexedRightFoldConnector .or available (T + 1)
        (fixedWidthSizeAt (T + 1) 1) rank.val :=
  getElem_predecessorHeadFormulaSchedule_connector_internal stateCount T
    configBase available tapeIndex target directionCode rank

/-- Exact raw compilation order of a horizon-length tape-read formula. -/
theorem compileRaw_readFormula_eq_schedule
    (tm : NTM k) (T configBase available : ℕ)
    (tape : TapeSlot k) (symbol : Γ) :
    BoolFormula.compileRaw available
        (readFormula tm T configBase tape symbol) =
      readFormulaSchedule (Fintype.card tm.Q) (k + 2) T configBase available
        tape.index.val (symbolIndex symbol).val :=
  compileRaw_readFormula_eq_schedule_internal tm T configBase available tape
    symbol

/-- Exact raw compilation order of a horizon-length predecessor-head formula. -/
theorem compileRaw_predecessorHeadFormula_eq_schedule
    (tm : NTM k) (T configBase available : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) (direction : Dir3) :
    BoolFormula.compileRaw available
        (predecessorHeadFormula tm T configBase tape target direction) =
      predecessorHeadFormulaSchedule (Fintype.card tm.Q) T configBase
        available tape.index.val target.val
          (match direction with
          | .left => 0
          | .right => 1
          | .stay => 2) :=
  compileRaw_predecessorHeadFormula_eq_schedule_internal tm T configBase
    available tape target direction

end Serializer

end CircuitUnrolling

end Complexity
