/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Defs

/-!
# Numeric schedules for transition-case formulas

One fixed transition case is flattened into six numeric phases: a choice
literal, one state-wire copy, one input read, a fixed finite list of work-tape
reads, one output read, and the conjunction suffix. Machine/view data is
compiled into natural indices and Boolean values before entering this layer.
No formula tree, configuration atom, tape slot, symbol, or bounded position is
stored by the schedule.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Gate count of a compiled choice literal. -/
def caseChoiceLiteralSize : Bool → ℕ
  | true => 1
  | false => 2

/-- Exact raw fragment for a compiled choice literal. -/
def caseChoiceLiteralSchedule
    (available choiceWire : ℕ) : Bool → CircuitCode.RawCircuit
  | true => [CircuitCode.RawGate.copy choiceWire]
  | false =>
      [CircuitCode.RawGate.copy choiceWire,
        CircuitCode.RawGate.copy available true]

/-- Common gate count of every compiled tape-read formula. -/
def caseReadSize (T : ℕ) : ℕ :=
  4 * (T + 1) + 1

/-- Number of conjuncts in a case with `workCount` work tapes. -/
def caseFormulaMemberCount (workCount : ℕ) : ℕ :=
  workCount + 4

/-- Number of gates in all case members, before the conjunction suffix. -/
def caseFormulaMembersSize (workCount T : ℕ) (choiceValue : Bool) : ℕ :=
  caseChoiceLiteralSize choiceValue + 1 +
    (workCount + 2) * caseReadSize T

/-- Total number of gates in a compiled case formula. -/
def caseFormulaScheduleSize (workCount T : ℕ) (choiceValue : Bool) : ℕ :=
  caseFormulaMembersSize workCount T choiceValue + 1 +
    caseFormulaMemberCount workCount

/-- Numeric member-size oracle in literal/state/input/work/output order. -/
def caseFormulaSizeAt
    (workCount T : ℕ) (choiceValue : Bool) (index : ℕ) : ℕ :=
  if index = 0 then caseChoiceLiteralSize choiceValue
  else if index = 1 then 1
  else if index < caseFormulaMemberCount workCount then caseReadSize T
  else 0

/-- Absolute state-wire reference reconstructed from its numeric state index. -/
def transitionStateRef (configBase stateIndex : ℕ) : ℕ :=
  configBase + stateIndex

/-- First gate position of the input-read member. -/
def caseInputReadAvailable (available : ℕ) (choiceValue : Bool) : ℕ :=
  available + caseChoiceLiteralSize choiceValue + 1

/-- First gate position of one work-read member. -/
def caseWorkReadAvailable
    (T available workIndex : ℕ) (choiceValue : Bool) : ℕ :=
  caseInputReadAvailable available choiceValue +
    caseReadSize T * (workIndex + 1)

/-- First gate position of the output-read member. -/
def caseOutputReadAvailable
    (workCount T available : ℕ) (choiceValue : Bool) : ℕ :=
  caseInputReadAvailable available choiceValue +
    caseReadSize T * (workCount + 1)

/-- Fixed-width stream of all work-tape read members. -/
def caseWorkReadGates
    (stateCount workCount T configBase available : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    CircuitCode.RawCircuit :=
  indexedGateBlocks workCount fun workIndex =>
    readFormulaSchedule stateCount (workCount + 2) T configBase
      (caseWorkReadAvailable T available workIndex choiceValue)
      (workIndex + 1) (workSymbolAt workIndex)

/-- Forward member stream for one fixed transition case. -/
def caseFormulaMemberGates
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    CircuitCode.RawCircuit :=
  caseChoiceLiteralSchedule available choiceWire choiceValue ++
    [CircuitCode.RawGate.copy (transitionStateRef configBase stateIndex)] ++
    readFormulaSchedule stateCount (workCount + 2) T configBase
      (caseInputReadAvailable available choiceValue) 0 inputSymbolIndex ++
    caseWorkReadGates stateCount workCount T configBase available choiceValue
      workSymbolAt ++
    readFormulaSchedule stateCount (workCount + 2) T configBase
      (caseOutputReadAvailable workCount T available choiceValue)
      (workCount + 1) outputSymbolIndex

/-- Complete raw schedule for one fixed transition-case formula. -/
def caseFormulaSchedule
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    CircuitCode.RawCircuit :=
  caseFormulaMemberGates stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt ++
    [CircuitCode.RawGate.constant 0 true] ++
    indexedRightFoldConnectors .and available
      (caseFormulaMemberCount workCount)
      (caseFormulaSizeAt workCount T choiceValue)

end Serializer

end CircuitUnrolling

end Complexity
