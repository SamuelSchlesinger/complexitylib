/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Defs

/-!
# Numeric schedules for atomic transition formulas -- definitions

This layer removes two more formula-syntax seams from the direct serializer.
`headAtCellFormulaGate` reconstructs its single raw gate from natural layout
indices, while `haltedOrSchedule` gives the fixed postorder wrapper around
already scheduled old-value and next-value fragments.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Single numeric gate saying whether an old head occupies a cell position.
The final cell, which has no represented old head, is constant false. -/
def headAtCellFormulaGate
    (stateCount T configBase tapeIndex position : ℕ) : CircuitCode.RawGate :=
  if position < T + 1 then
    CircuitCode.RawGate.copy
      (transitionHeadRef stateCount T configBase tapeIndex position)
  else CircuitCode.RawGate.constant 0 false

/-- Raw postorder wrapper for `haltedOrFormula` around two already compiled
fragments. The old fragment begins after the first halt-wire copy; the next
fragment begins after the complete left conjunct and the negated halt test. -/
def haltedOrSchedule (haltWire available : ℕ)
    (oldSchedule nextSchedule : CircuitCode.RawCircuit) :
    CircuitCode.RawCircuit :=
  [CircuitCode.RawGate.copy haltWire] ++ oldSchedule ++
    [{ op := .and
       input₀ := available
       input₁ := available + oldSchedule.length
       negated₀ := false
       negated₁ := false },
     CircuitCode.RawGate.copy haltWire,
     CircuitCode.RawGate.copy (available + oldSchedule.length + 2) true] ++
    nextSchedule ++
    [{ op := .and
       input₀ := available + oldSchedule.length + 3
       input₁ := available + oldSchedule.length + nextSchedule.length + 3
       negated₀ := false
       negated₁ := false },
     { op := .or
       input₀ := available + oldSchedule.length + 1
       input₁ := available + oldSchedule.length + nextSchedule.length + 4
       negated₀ := false
       negated₁ := false }]

end Serializer

end CircuitUnrolling

end Complexity
