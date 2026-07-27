/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect.Defs

/-!
# Numeric schedules for moved-head formulas -- definitions

A moved-head formula is a three-member disjunction, one member for each head
direction. Each member consists of an effect-formula schedule, a numeric
predecessor-head schedule, and one conjunction gate. The complete stream then
adds the false identity and three reverse disjunction connectors.

The schedule state is entirely natural-number and Boolean data. Machine cases,
tape slots, directions, bounded indices, formula trees, and list cursors occur
only in the compile-time extractor or the proof adapter.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Number of fixed movement directions in left/right/stay order. -/
def movedHeadDirectionCount : ℕ := 3

/-- Compile-time case-selection oracle, indexed by a numeric direction code
and then by a numeric transition-case index. -/
noncomputable def movedHeadCaseSelectedAt
    (tm : NTM k) (tape : TapeSlot k) : ℕ → ℕ → Bool
  | 0 => effectCaseSelectedAt tm fun effect =>
      decide (effect.move tape = .left)
  | 1 => effectCaseSelectedAt tm fun effect =>
      decide (effect.move tape = .right)
  | 2 => effectCaseSelectedAt tm fun effect =>
      decide (effect.move tape = .stay)
  | _ => fun _ => false

/-- Gate count of every predecessor-head child. -/
def movedHeadPredecessorSize (T : ℕ) : ℕ :=
  2 * (T + 1) + 1

/-- Gate count of the effect child for one numeric direction. -/
def movedHeadEffectSizeAt
    (caseCount workCount T : ℕ) (selectedAt : ℕ → ℕ → Bool)
    (choiceAt : ℕ → Bool) (directionCode : ℕ) : ℕ :=
  effectFormulaScheduleSize caseCount workCount T
    (selectedAt directionCode) choiceAt

/-- Total size oracle for the three conjunction members. -/
def movedHeadMemberSizeAt
    (caseCount workCount T : ℕ) (selectedAt : ℕ → ℕ → Bool)
    (choiceAt : ℕ → Bool) (directionCode : ℕ) : ℕ :=
  if directionCode < movedHeadDirectionCount then
    movedHeadEffectSizeAt caseCount workCount T selectedAt choiceAt
        directionCode +
      movedHeadPredecessorSize T + 1
  else 0

/-- First gate position of one direction member. -/
def movedHeadMemberAvailable
    (caseCount workCount T available : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (directionCode : ℕ) : ℕ :=
  available + prefixSize
    (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
    directionCode

/-- First gate position of one direction's predecessor-head child. -/
def movedHeadPredecessorAvailable
    (caseCount workCount T available : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (directionCode : ℕ) : ℕ :=
  movedHeadMemberAvailable caseCount workCount T available selectedAt choiceAt
      directionCode +
    movedHeadEffectSizeAt caseCount workCount T selectedAt choiceAt
      directionCode

/-- Final conjunction gate of one direction member. -/
def movedHeadConjunctionGate
    (caseCount workCount T available : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (directionCode : ℕ) : CircuitCode.RawGate :=
  { op := .and
    input₀ :=
      movedHeadMemberAvailable caseCount workCount T available selectedAt
          choiceAt directionCode +
        movedHeadEffectSizeAt caseCount workCount T selectedAt choiceAt
          directionCode - 1
    input₁ :=
      movedHeadPredecessorAvailable caseCount workCount T available selectedAt
          choiceAt directionCode +
        movedHeadPredecessorSize T - 1
    negated₀ := false
    negated₁ := false }

/-- Numeric raw fragment for one left/right/stay conjunction member. -/
def movedHeadMemberBlock
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (directionCode : ℕ) :
    CircuitCode.RawCircuit :=
  effectFormulaSchedule caseCount stateCount workCount T configBase choiceWire
      (movedHeadMemberAvailable caseCount workCount T available selectedAt
        choiceAt directionCode)
      (selectedAt directionCode) choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt ++
    predecessorHeadFormulaSchedule stateCount T configBase
      (movedHeadPredecessorAvailable caseCount workCount T available selectedAt
        choiceAt directionCode)
      tapeIndex target directionCode ++
    [movedHeadConjunctionGate caseCount workCount T available selectedAt
      choiceAt directionCode]

/-- Forward stream of the three direction-member blocks. -/
def movedHeadMemberGates
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks movedHeadDirectionCount fun directionCode =>
    movedHeadMemberBlock caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt directionCode

/-- Complete numeric raw schedule for a moved-head formula. -/
def movedHeadFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) : CircuitCode.RawCircuit :=
  movedHeadMemberGates caseCount stateCount workCount T configBase choiceWire
      available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt ++
    [CircuitCode.RawGate.constant 0 false] ++
    indexedRightFoldConnectors .or available movedHeadDirectionCount
      (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)

/-- Exact gate count of the complete moved-head schedule. -/
def movedHeadFormulaScheduleSize
    (caseCount workCount T : ℕ) (selectedAt : ℕ → ℕ → Bool)
    (choiceAt : ℕ → Bool) : ℕ :=
  prefixSize
      (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
      movedHeadDirectionCount +
    1 + movedHeadDirectionCount

end Serializer

end CircuitUnrolling

end Complexity
