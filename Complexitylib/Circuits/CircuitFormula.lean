/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.CircuitFormula.Defs
public import Complexitylib.Circuits.CircuitFormula.Internal

/-!
# Unfolding fan-in-two circuit outputs into Boolean formulas

This module recursively unfolds a selected wire or output of a typed fan-in-two
AND/OR circuit into a `BoolFormula`. The translation preserves evaluation
exactly. Since edge negations are explicit formula nodes, formula depth is at
most twice the corresponding circuit depth.

Circuit gates form a DAG, while formulas are trees. Consequently this unfolding
duplicates shared subcircuits, and these theorems deliberately make no formula
size claim.

## Main results

- `Complexity.Circuit.eval_wireFormula` — exact semantics for an unfolded wire.
- `Complexity.Circuit.eval_outputFormula` — exact semantics for a selected output.
- `Complexity.Circuit.vars_outputFormula_lt` — every unfolded variable is
  below the circuit's input arity.
- `Complexity.Circuit.depth_wireFormula_le` — wire-formula depth is at most twice
  wire depth.
- `Complexity.Circuit.depth_outputFormula_le_outputDepth` — output-formula depth
  is at most twice the selected output depth.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

/-- Conditional formula negation agrees with Boolean exclusive-or semantics. -/
theorem eval_negateIf (assignment : ℕ → Bool)
    (negated : Bool) (formula : BoolFormula) :
    eval assignment (negateIf negated formula) =
      negated.xor (eval assignment formula) :=
  eval_negateIf_internal assignment negated formula

end BoolFormula

namespace Gate

/-- Replacing a fan-in-two gate's source wires by formulas preserves its
evaluation. -/
theorem eval_toBoolFormula {W : ℕ}
    (gate : Gate Basis.andOr2 W) (wireFormula : Fin W → BoolFormula)
    (assignment : ℕ → Bool) :
    BoolFormula.eval assignment (gate.toBoolFormula wireFormula) =
      gate.eval fun wire => BoolFormula.eval assignment (wireFormula wire) :=
  eval_toBoolFormula_internal gate wireFormula assignment

end Gate


namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

/-- Unfolding an internal circuit wire into a formula preserves its value. -/
theorem eval_wireFormula
    (circuit : Circuit Basis.andOr2 N M G) (assignment : ℕ → Bool)
    (wire : Fin (N + G)) :
    BoolFormula.eval assignment (circuit.wireFormula wire) =
      circuit.wireValue (fun input => assignment input.val) wire :=
  eval_wireFormula_internal circuit assignment wire

/-- Unfolding one selected circuit output into a formula preserves that output's
value exactly. -/
theorem eval_outputFormula
    (circuit : Circuit Basis.andOr2 N M G) (assignment : ℕ → Bool)
    (output : Fin M) :
    BoolFormula.eval assignment (circuit.outputFormula output) =
      circuit.eval (fun input => assignment input.val) output :=
  eval_outputFormula_internal circuit assignment output

/-- Every variable in an unfolded wire formula is a primary-input index. -/
theorem vars_wireFormula_lt
    (circuit : Circuit Basis.andOr2 N M G) (wire : Fin (N + G)) :
    ∀ index ∈ (circuit.wireFormula wire).vars, index < N :=
  vars_wireFormula_lt_internal circuit wire

/-- Every variable in an unfolded output formula lies below the circuit's
declared input arity. -/
theorem vars_outputFormula_lt
    (circuit : Circuit Basis.andOr2 N M G) (output : Fin M) :
    ∀ index ∈ (circuit.outputFormula output).vars, index < N :=
  vars_outputFormula_lt_internal circuit output

/-- The unfolded formula below a wire has depth at most twice the wire's DAG
depth. The factor two accounts for an edge negation followed by its gate. -/
theorem depth_wireFormula_le
    (circuit : Circuit Basis.andOr2 N M G) (wire : Fin (N + G)) :
    (circuit.wireFormula wire).depth ≤ 2 * circuit.wireDepth wire :=
  depth_wireFormula_le_internal circuit wire

/-- The formula for a selected output has depth at most twice that output's
circuit depth. No formula-size bound is asserted because DAG sharing is
duplicated by unfolding. -/
theorem depth_outputFormula_le_outputDepth
    (circuit : Circuit Basis.andOr2 N M G) (output : Fin M) :
    (circuit.outputFormula output).depth ≤
      2 * circuit.outputDepth output :=
  depth_outputFormula_le_outputDepth_internal circuit output

end Circuit

end Complexity
