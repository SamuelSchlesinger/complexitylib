/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Defs

/-!
# Numeric transition-formula schedules

This definitions layer flattens the two position-indexed formulas used most
often by transition serialization. Every run-time parameter is a natural
number: state and tape counts, layout bases, tape/symbol indices, positions,
and a three-valued movement code. No formula tree, configuration atom, or
bounded index occurs in the schedule state.

A read member always occupies three gates: copies of its head and cell wires,
then their conjunction. A predecessor-head member occupies one gate: either a
head-wire copy or false. Both streams finish with the existing numeric
right-fold disjunction suffix.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Constant fixed-width size oracle on the first `count` indices. -/
def fixedWidthSizeAt (count width index : ℕ) : ℕ :=
  if index < count then width else 0

/-- Absolute head-wire reference reconstructed from numeric layout data. -/
def transitionHeadRef (stateCount T configBase tapeIndex position : ℕ) : ℕ :=
  configBase + (stateCount + tapeIndex * (T + 1) + position)

/-- Absolute cell-wire reference reconstructed from numeric layout data. -/
def transitionCellRef
    (stateCount tapeCount T configBase tapeIndex position symbolIndex : ℕ) : ℕ :=
  configBase + (stateCount + tapeCount * (T + 1) +
    (tapeIndex * (T + 2) + position) * 4 + symbolIndex)

/-- Three-gate fragment for one candidate head position in a read formula. -/
def readFormulaMemberBlock
    (stateCount tapeCount T configBase available tapeIndex symbolIndex
      position : ℕ) : CircuitCode.RawCircuit :=
  [CircuitCode.RawGate.copy
      (transitionHeadRef stateCount T configBase tapeIndex position),
    CircuitCode.RawGate.copy
      (transitionCellRef stateCount tapeCount T configBase tapeIndex position
        symbolIndex),
    { op := .and
      input₀ := available + 3 * position
      input₁ := available + 3 * position + 1
      negated₀ := false
      negated₁ := false }]

/-- Forward, position-indexed member stream of a read formula. -/
def readFormulaMemberGates
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    CircuitCode.RawCircuit :=
  indexedGateBlocks (T + 1) fun position =>
    readFormulaMemberBlock stateCount tapeCount T configBase available
      tapeIndex symbolIndex position

/-- Complete raw schedule for a read formula. -/
def readFormulaSchedule
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    CircuitCode.RawCircuit :=
  readFormulaMemberGates stateCount tapeCount T configBase available
      tapeIndex symbolIndex ++
    [CircuitCode.RawGate.constant 0 false] ++
    indexedRightFoldConnectors .or available (T + 1)
      (fixedWidthSizeAt (T + 1) 3)

/-- Move a natural head position according to a numeric direction code:
`0 = left`, `1 = right`, and every other code means stay. -/
def movedHeadPositionCode (position directionCode : ℕ) : ℕ :=
  if directionCode = 0 then position - 1
  else if directionCode = 1 then position + 1
  else position

/-- One gate for a candidate predecessor head position. -/
def predecessorHeadMemberGate
    (stateCount T configBase tapeIndex target directionCode source : ℕ) :
    CircuitCode.RawGate :=
  if movedHeadPositionCode source directionCode = target then
    CircuitCode.RawGate.copy
      (transitionHeadRef stateCount T configBase tapeIndex source)
  else
    CircuitCode.RawGate.constant 0 false

/-- Forward, source-indexed member stream of a predecessor-head formula. -/
def predecessorHeadMemberGates
    (stateCount T configBase tapeIndex target directionCode : ℕ) :
    CircuitCode.RawCircuit :=
  indexedGateBlocks (T + 1) fun source =>
    [predecessorHeadMemberGate stateCount T configBase tapeIndex target
      directionCode source]

/-- Complete raw schedule for a predecessor-head formula. -/
def predecessorHeadFormulaSchedule
    (stateCount T configBase available tapeIndex target directionCode : ℕ) :
    CircuitCode.RawCircuit :=
  predecessorHeadMemberGates stateCount T configBase tapeIndex target
      directionCode ++
    [CircuitCode.RawGate.constant 0 false] ++
    indexedRightFoldConnectors .or available (T + 1)
      (fixedWidthSizeAt (T + 1) 1)

end Serializer

end CircuitUnrolling

end Complexity
