/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Fragment.Defs
public import Complexitylib.Circuits.Formula

/-!
# Compile Boolean formulas to raw circuit fragments

This file defines a proof-free compiler from `BoolFormula` trees to appendable
`CircuitCode.RawCircuit` fragments. Given `available` existing wires, the
compiler emits one new gate per formula node. Variables are absolute references
into the existing prefix, and the last new wire carries the formula value.

Variables are copied through a duplicated AND gate. Constants use an arbitrary
existing wire together with its negation, while formula negation uses the raw
gate's free edge-negation flags. Binary formulas are emitted in postorder.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

/-- Absolute wire carrying the output of a compiled formula fragment. -/
def rawOutputWire (available : ℕ) (formula : BoolFormula) : ℕ :=
  available + formula.size - 1

/-- Compile a formula after `available` existing wires.

The result is a fragment rather than a complete circuit: it may be appended to
an existing raw prefix without renumbering its absolute wire references. -/
def compileRaw (available : ℕ) : BoolFormula → CircuitCode.RawCircuit
  | .var i => [CircuitCode.RawGate.copy i]
  | .tru => [CircuitCode.RawGate.constant 0 true]
  | .fls => [CircuitCode.RawGate.constant 0 false]
  | .neg formula =>
      compileRaw available formula ++
        [CircuitCode.RawGate.copy (rawOutputWire available formula) true]
  | .conj left right =>
      compileRaw available left ++
        (compileRaw (available + left.size) right ++
          [{ op := .and
             input₀ := rawOutputWire available left
             input₁ := rawOutputWire (available + left.size) right
             negated₀ := false
             negated₁ := false }])
  | .disj left right =>
      compileRaw available left ++
        (compileRaw (available + left.size) right ++
          [{ op := .or
             input₀ := rawOutputWire available left
             input₁ := rawOutputWire (available + left.size) right
             negated₀ := false
             negated₁ := false }])

end BoolFormula

end Complexity
