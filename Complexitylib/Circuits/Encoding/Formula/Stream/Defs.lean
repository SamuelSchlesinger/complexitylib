/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Batch.Defs

/-!
# Stack-free streams for finite Boolean folds — definitions

Right-associated finite conjunctions and disjunctions have linear tree depth.
Their raw compilation nevertheless has a simple streaming order: compile every
member from left to right, emit one terminal constant, then emit the binary
connectors from right to left. This module names the connector suffix used by
that decomposition.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

/-- Tree size shared by a right-associated conjunction or disjunction over
`formulas`. -/
def rightFoldSize (formulas : List BoolFormula) : ℕ :=
  1 + (formulas.map fun formula => formula.size + 1).sum

/-- Connector gates completing a right-associated finite Boolean fold.

The recursive call emits the deeper, right-hand connectors first. The final
gate combines the current member output with the completed tail output. -/
def rightFoldConnectors (op : AndOrOp) (available : ℕ) :
    List BoolFormula → CircuitCode.RawCircuit
  | [] => []
  | formula :: formulas =>
      rightFoldConnectors op (available + formula.size) formulas ++
        [{ op
           input₀ := rawOutputWire available formula
           input₁ := available + formula.size + rightFoldSize formulas - 1
           negated₀ := false
           negated₁ := false }]

/-- Explicit stack-free raw stream for a finite Boolean fold. Members are
compiled forward, the identity constant is emitted once, and connectors are
emitted in reverse member order. -/
def compileRawRightFold (op : AndOrOp) (identity : Bool)
    (available : ℕ) (formulas : List BoolFormula) : CircuitCode.RawCircuit :=
  (compileRawOutputs available formulas).circuit ++
    [CircuitCode.RawGate.constant 0 identity] ++
    rightFoldConnectors op available formulas

end BoolFormula

end Complexity
