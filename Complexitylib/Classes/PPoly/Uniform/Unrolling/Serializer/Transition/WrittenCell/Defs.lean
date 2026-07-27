/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Atomic.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect.Defs

/-!
# Numeric schedules for written-cell formulas

A written-cell formula contains one variable-size selected-write effect and a
fixed Boolean wrapper. This layer places the effect schedule after one numeric
head-at-cell gate, then emits six fixed suffix gates by an increasing natural
phase counter. Layout addresses, phase bases, and the effect descriptors are
all natural numbers or Booleans.

The fixed machine, writable tape, and symbol are used only to derive the
compile-time selection oracle. No run-time schedule value contains a formula,
bounded index, transition case, tape slot, symbol, or list cursor.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Compile-time selection oracle for cases writing `symbol` on `tape`. -/
noncomputable def writtenCellEffectSelectedAt (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) : ℕ → Bool :=
  effectCaseSelectedAt tm fun effect =>
    decide ((effect.write tape).toΓ = symbol)

/-- Gate count of the selected-write effect nested in a written-cell formula. -/
def writtenCellEffectSize
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) : ℕ :=
  effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt

/-- Left conjunct gate combining `atHead` with the selected-write effect. -/
def writtenCellLeftAndGate (available effectSize : ℕ) :
    CircuitCode.RawGate :=
  { op := .and
    input₀ := available
    input₁ := available + effectSize
    negated₀ := false
    negated₁ := false }

/-- Negation gate following the second copy of `atHead`. -/
def writtenCellNegatedHeadGate (available effectSize : ℕ) :
    CircuitCode.RawGate :=
  CircuitCode.RawGate.copy (available + effectSize + 2) true

/-- Old-cell variable gate reconstructed from numeric layout indices. -/
def writtenCellOldValueGate
    (stateCount tapeCount T configBase tapeIndex position symbolIndex : ℕ) :
    CircuitCode.RawGate :=
  CircuitCode.RawGate.copy
    (transitionCellRef stateCount tapeCount T configBase tapeIndex position
      symbolIndex)

/-- Right conjunct gate combining `not atHead` with the old cell value. -/
def writtenCellRightAndGate (available effectSize : ℕ) :
    CircuitCode.RawGate :=
  { op := .and
    input₀ := available + effectSize + 3
    input₁ := available + effectSize + 4
    negated₀ := false
    negated₁ := false }

/-- Final disjunction gate combining the write and preservation branches. -/
def writtenCellFinalOrGate (available effectSize : ℕ) :
    CircuitCode.RawGate :=
  { op := .or
    input₀ := available + effectSize + 1
    input₁ := available + effectSize + 5
    negated₀ := false
    negated₁ := false }

/-- One of the six fixed suffix gates, selected by a natural phase code.
Codes `0, ..., 5` mean left AND, second head test, head negation, old value,
right AND, and final OR respectively. -/
def writtenCellSuffixGate
    (stateCount tapeCount T configBase available tapeIndex position symbolIndex
      effectSize phase : ℕ) : CircuitCode.RawGate :=
  if phase = 0 then writtenCellLeftAndGate available effectSize
  else if phase = 1 then
    headAtCellFormulaGate stateCount T configBase tapeIndex position
  else if phase = 2 then writtenCellNegatedHeadGate available effectSize
  else if phase = 3 then
    writtenCellOldValueGate stateCount tapeCount T configBase tapeIndex position
      symbolIndex
  else if phase = 4 then writtenCellRightAndGate available effectSize
  else writtenCellFinalOrGate available effectSize

/-- Six-gate fixed suffix driven by an increasing natural phase counter. -/
def writtenCellSuffixGates
    (stateCount tapeCount T configBase available tapeIndex position symbolIndex
      effectSize : ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks 6 fun phase =>
    [writtenCellSuffixGate stateCount tapeCount T configBase available tapeIndex
      position symbolIndex effectSize phase]

/-- Complete numeric schedule for a written-cell formula. -/
def writtenCellSchedule
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    CircuitCode.RawCircuit :=
  let effectSize := writtenCellEffectSize caseCount workCount T selectedAt choiceAt
  [headAtCellFormulaGate stateCount T configBase tapeIndex position] ++
    (effectFormulaSchedule caseCount stateCount workCount T configBase
        choiceWire (available + 1) selectedAt choiceAt stateIndexAt
        inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt ++
      writtenCellSuffixGates stateCount (workCount + 2) T configBase available
        tapeIndex position symbolIndex effectSize)

/-- Exact gate count of the complete numeric written-cell schedule. -/
def writtenCellScheduleSize
    (caseCount workCount T : ℕ) (selectedAt choiceAt : ℕ → Bool) : ℕ :=
  writtenCellEffectSize caseCount workCount T selectedAt choiceAt + 7

end Serializer

end CircuitUnrolling

end Complexity
