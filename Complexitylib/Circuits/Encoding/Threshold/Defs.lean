/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Fragment.Defs

/-!
# Raw threshold-circuit fragments

This file defines an appendable raw circuit that tests whether at least a
specified number of existing Boolean wires are true. The construction is the
standard unary dynamic program. Its state after reading `i` inputs records, for
each `r`, whether at least `r` of those inputs were true.

Two gates update each state cell:

`next (r + 1) = previous (r + 1) OR (input AND previous r)`.

The fragment starts with reusable false and true wires, emits the table in
row-major order, and ends with a copy of the requested final state. Thus it has
exactly `3 + 2 * k * threshold` gates for `k` referenced inputs.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Threshold

/-- The constant-false wire at the start of a threshold fragment. -/
def falseWire (available : ℕ) : ℕ :=
  available

/-- The constant-true wire at the start of a threshold fragment. -/
def trueWire (available : ℕ) : ℕ :=
  available + 1

/-- The conjunction wire for table cell `(inputRow, thresholdColumn)`. -/
def andWire (available threshold inputRow thresholdColumn : ℕ) : ℕ :=
  available + 2 + 2 * (inputRow * threshold + thresholdColumn)

/-- The completed dynamic-programming state wire for a table cell. -/
def cellWire (available threshold inputRow thresholdColumn : ℕ) : ℕ :=
  andWire available threshold inputRow thresholdColumn + 1

/-- Wire representing whether the first `inputCount` inputs contain at least
`required` true values.

The zero threshold is always true. Before any input has been processed, every
positive threshold is false. All other states are table-cell outputs. -/
def stateWire (available threshold : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => trueWire available
  | 0, _ + 1 => falseWire available
  | inputCount + 1, required + 1 =>
      cellWire available threshold inputCount required

/-- The two raw gates that update one unary threshold-table cell. -/
def cellGates (available threshold inputRow thresholdColumn input : ℕ) :
    RawCircuit :=
  [{ op := .and
     input₀ := input
     input₁ := stateWire available threshold inputRow thresholdColumn
     negated₀ := false
     negated₁ := false },
   { op := .or
     input₀ := stateWire available threshold inputRow (thresholdColumn + 1)
     input₁ := andWire available threshold inputRow thresholdColumn
     negated₀ := false
     negated₁ := false }]

/-- Emit the first `columnCount` cells of one table row. -/
def rowPrefix (available threshold inputRow input : ℕ) : ℕ → RawCircuit
  | 0 => []
  | columnCount + 1 =>
      rowPrefix available threshold inputRow input columnCount ++
        cellGates available threshold inputRow columnCount input

/-- Emit successive table rows, starting at `inputRow`. -/
def rows (available threshold inputRow : ℕ) :
    (inputCount : ℕ) → (Fin inputCount → ℕ) → RawCircuit
  | 0, _ => []
  | inputCount + 1, refs =>
      rowPrefix available threshold inputRow (refs 0) threshold ++
        rows available threshold (inputRow + 1) inputCount (fun i => refs i.succ)

/-- Absolute wire carrying the threshold fragment's final output. -/
def outputWire (available inputCount threshold : ℕ) : ℕ :=
  available + 2 + 2 * inputCount * threshold

/-- Compile an at-least-threshold test over existing absolute wire references.

The result is appendable without renumbering. Its output is true exactly when
at least `threshold` of the referenced wires are true. -/
def compileRaw (available threshold : ℕ) {inputCount : ℕ}
    (refs : Fin inputCount → ℕ) : RawCircuit :=
  [RawGate.constant 0 false, RawGate.constant 0 true] ++
    rows available threshold 0 inputCount refs ++
      [RawGate.copy (stateWire available threshold inputCount threshold)]

end Threshold

end CircuitCode

end Complexity
