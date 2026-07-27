/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect.Internal

/-!
# Numeric schedules for transition-effect formulas

This module exposes the case-indexed raw stream for `effectFormula`. The
machine-dependent transition table is reduced to compile-time Boolean and
natural-number oracles. Selected cases use the numeric case schedule,
unselected cases emit one false gate, and a numeric reverse-OR suffix completes
the disjunction.

## Main results

- `length_effectFormulaSchedule` gives the exact numeric gate count.
- `getElem_effectFormulaSchedule_identity` and
  `getElem_effectFormulaSchedule_connector` identify the final fold phases.
- `compileRaw_effectFormula_eq_schedule` proves literal raw-list equality.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- An in-range case block has exactly the size advertised by the total
numeric case-size oracle. -/
@[simp] theorem length_effectFormulaCaseBlock
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (caseIndex : ℕ)
    (hcase : caseIndex < caseCount) :
    (effectFormulaCaseBlock caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt caseIndex).length =
        effectFormulaSizeAt caseCount workCount T selectedAt choiceAt
          caseIndex :=
  length_effectFormulaCaseBlock_internal caseCount stateCount workCount T
    configBase choiceWire available selectedAt choiceAt stateIndexAt
    inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt caseIndex hcase

/-- The forward member phase has the prefix-sum of all numeric case sizes. -/
@[simp] theorem length_effectFormulaCaseGates
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (effectFormulaCaseGates caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt).length =
        prefixSize
          (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
          caseCount :=
  length_effectFormulaCaseGates_internal caseCount stateCount workCount T
    configBase choiceWire available selectedAt choiceAt stateIndexAt
    inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- The complete effect schedule is all member gates, one false identity, and
one connector per case. -/
@[simp] theorem length_effectFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (effectFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt).length =
        effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt :=
  length_effectFormulaSchedule_internal caseCount stateCount workCount T
    configBase choiceWire available selectedAt choiceAt stateIndexAt
    inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- The gate immediately after all case blocks is the false disjunction
identity. -/
theorem getElem_effectFormulaSchedule_identity
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (effectFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt)[
        prefixSize
          (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
          caseCount]'(by
            rw [length_effectFormulaSchedule]
            simp [effectFormulaScheduleSize]
            omega) = CircuitCode.RawGate.constant 0 false :=
  getElem_effectFormulaSchedule_identity_internal caseCount stateCount workCount
    T configBase choiceWire available selectedAt choiceAt stateIndexAt
    inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- Connector rank is an upward natural counter visiting source cases in
reverse order. -/
theorem getElem_effectFormulaSchedule_connector
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (rank : Fin caseCount) :
    (effectFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt)[
        prefixSize
            (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
            caseCount +
          1 + rank.val]'(by
            rw [length_effectFormulaSchedule]
            simp [effectFormulaScheduleSize]) =
      indexedRightFoldConnector .or available caseCount
        (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
        rank.val :=
  getElem_effectFormulaSchedule_connector_internal caseCount stateCount
    workCount T configBase choiceWire available selectedAt choiceAt stateIndexAt
    inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt rank

/-- Exact raw compilation order of a transition-effect formula. All dynamic
schedule inputs are natural numbers or Booleans; the machine-dependent case
table is fixed by `tm`. -/
theorem compileRaw_effectFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (selects : TransitionEffect tm → Bool) :
    BoolFormula.compileRaw available
        (effectFormula tm T configBase choiceWire selects) =
      effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm) :=
  compileRaw_effectFormula_eq_schedule_internal tm T configBase choiceWire
    available selects

end Serializer

end CircuitUnrolling

end Complexity
