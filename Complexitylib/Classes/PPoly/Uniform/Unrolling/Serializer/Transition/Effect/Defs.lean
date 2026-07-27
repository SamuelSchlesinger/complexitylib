/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case.Defs

/-!
# Numeric schedules for transition-effect formulas

An effect formula is a finite disjunction over the fixed transition cases of
the compiled machine. This layer describes its raw stream using a natural case
counter, Boolean selection and choice oracles, and natural state and symbol
indices. Selected members use the numeric case-formula schedule; unselected
members are single false gates.

The machine-dependent case table is inspected only by compile-time numeric
extractors. The streaming schedule itself carries no transition case, effect,
formula tree, bounded index, or list traversal state.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Numeric selection bit of one fixed machine transition case. -/
noncomputable def effectCaseSelectedAt (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ) : Bool :=
  if hcase : caseIndex < (transitionCases tm).length then
    selects ((transitionCases tm)[caseIndex]'hcase).effect
  else false

/-- Numeric choice bit of one fixed machine transition case. -/
noncomputable def effectCaseChoiceAt (tm : NTM k) (caseIndex : ℕ) : Bool :=
  if hcase : caseIndex < (transitionCases tm).length then
    ((transitionCases tm)[caseIndex]'hcase).choice
  else false

/-- Numeric state index of one fixed machine transition case. -/
noncomputable def effectCaseStateIndexAt
    (tm : NTM k) (caseIndex : ℕ) : ℕ :=
  if hcase : caseIndex < (transitionCases tm).length then
    stateIndex tm ((transitionCases tm)[caseIndex]'hcase).state
  else 0

/-- Numeric input-symbol index of one fixed machine transition case. -/
noncomputable def effectCaseInputSymbolIndexAt
    (tm : NTM k) (caseIndex : ℕ) : ℕ :=
  if hcase : caseIndex < (transitionCases tm).length then
    (symbolIndex ((transitionCases tm)[caseIndex]'hcase).inputRead).val
  else 0

/-- Numeric output-symbol index of one fixed machine transition case. -/
noncomputable def effectCaseOutputSymbolIndexAt
    (tm : NTM k) (caseIndex : ℕ) : ℕ :=
  if hcase : caseIndex < (transitionCases tm).length then
    (symbolIndex ((transitionCases tm)[caseIndex]'hcase).outputRead).val
  else 0

/-- Numeric work-symbol index of one fixed case and work-tape position. -/
noncomputable def effectCaseWorkSymbolIndexAt
    (tm : NTM k) (caseIndex workIndex : ℕ) : ℕ :=
  if hcase : caseIndex < (transitionCases tm).length then
    if hwork : workIndex < k then
      (symbolIndex (((transitionCases tm)[caseIndex]'hcase).workRead
        ⟨workIndex, hwork⟩)).val
    else 0
  else 0

/-- Gate count of one effect-disjunction member. -/
def effectFormulaCaseSize
    (workCount T : ℕ) (selected choiceValue : Bool) : ℕ :=
  if selected then caseFormulaScheduleSize workCount T choiceValue else 1

/-- Total numeric case-size oracle, returning zero beyond `caseCount`. -/
def effectFormulaSizeAt
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool)
    (caseIndex : ℕ) : ℕ :=
  if caseIndex < caseCount then
    effectFormulaCaseSize workCount T (selectedAt caseIndex)
      (choiceAt caseIndex)
  else 0

/-- First gate position of one case member in the effect disjunction. -/
def effectFormulaCaseAvailable
    (caseCount workCount T available : ℕ)
    (selectedAt choiceAt : ℕ → Bool) (caseIndex : ℕ) : ℕ :=
  available + prefixSize
    (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt) caseIndex

/-- Numeric raw fragment for one effect-disjunction member. -/
def effectFormulaCaseBlock
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (caseIndex : ℕ) :
    CircuitCode.RawCircuit :=
  if selectedAt caseIndex then
    caseFormulaSchedule stateCount workCount T configBase choiceWire
      (effectFormulaCaseAvailable caseCount workCount T available selectedAt
        choiceAt caseIndex)
      (stateIndexAt caseIndex) (inputSymbolIndexAt caseIndex)
      (outputSymbolIndexAt caseIndex) (choiceAt caseIndex)
      (workSymbolIndexAt caseIndex)
  else [CircuitCode.RawGate.constant 0 false]

/-- Forward numeric stream of all effect-disjunction case members. -/
def effectFormulaCaseGates
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    CircuitCode.RawCircuit :=
  indexedGateBlocks caseCount fun caseIndex =>
    effectFormulaCaseBlock caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt caseIndex

/-- Complete numeric raw schedule for a transition-effect formula. -/
def effectFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    CircuitCode.RawCircuit :=
  effectFormulaCaseGates caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt ++
    [CircuitCode.RawGate.constant 0 false] ++
    indexedRightFoldConnectors .or available caseCount
      (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)

/-- Exact gate count of the complete numeric effect-formula schedule. -/
def effectFormulaScheduleSize
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) : ℕ :=
  prefixSize (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
      caseCount +
    1 + caseCount

end Serializer

end CircuitUnrolling

end Complexity
