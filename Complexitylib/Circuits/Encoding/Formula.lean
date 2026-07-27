/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Internal

/-!
# Correctness of Boolean-formula raw compilation

This module exposes the exact size, topological well-formedness, and iterative
evaluation guarantees for `BoolFormula.compileRaw`. A fragment starts after an
explicit number of available wires, so its variables may refer directly to
primary inputs or to any gate emitted by an earlier fragment.

Correctness assumes at least one available wire because constant gates use an
existing wire together with its negation. This matches positive-arity typed
circuits; circuit families handle their zero-input member separately.

## Main definitions and results

- `BoolFormula.compileRaw`: the existing-wire-aware proof-free compiler.
- `BoolFormula.length_compileRaw`: exactly one gate is emitted per formula node.
- `BoolFormula.topologicallyWellFormed_compileRaw`: all new references point backward.
- `BoolFormula.evalAux?_compileRaw_of_agree`: sparse-variable semantic
  correctness; `evalAux?_compileRaw` is the all-existing-wires corollary.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

/-- Formula compilation emits exactly one raw gate per syntax-tree node. -/
@[simp] theorem length_compileRaw (available : ℕ) (formula : BoolFormula) :
    (compileRaw available formula).length = formula.size :=
  length_compileRaw_internal available formula

/-- The output wire lies inside the newly compiled fragment. -/
theorem rawOutputWire_lt (available : ℕ) (formula : BoolFormula) :
    rawOutputWire available formula < available + formula.size :=
  rawOutputWire_lt_internal available formula

/-- A compiled formula's output is never before its existing-wire prefix. -/
theorem le_rawOutputWire (available : ℕ) (formula : BoolFormula) :
    available ≤ rawOutputWire available formula := by
  have hsize := formula.one_le_size
  simp only [rawOutputWire]
  omega

/-- The output wire is the final wire emitted by formula compilation. -/
theorem rawOutputWire_eq (available : ℕ) (formula : BoolFormula) :
    rawOutputWire available formula =
      available + (compileRaw available formula).length - 1 :=
  rawOutputWire_eq_internal available formula

/-- If every variable names an existing wire, a compiled fragment only
references the existing prefix or earlier gates in the same fragment. -/
theorem topologicallyWellFormed_compileRaw (available : ℕ) [NeZero available]
    (formula : BoolFormula) (hvars : ∀ i ∈ formula.vars, i < available) :
    (compileRaw available formula).TopologicallyWellFormed available :=
  topologicallyWellFormed_compileRaw_internal available formula hvars

/-- Compiled formula evaluation only requires semantic agreement on the wires
actually named by the formula. It appends exactly `formula.size` entries,
preserves the existing memo array, and places the formula value on the final
new wire. -/
theorem evalAux?_compileRaw_of_agree (available : ℕ) [NeZero available]
    (formula : BoolFormula) (assignment : ℕ → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hvars : ∀ i ∈ formula.vars, i < available)
    (hagree : ∀ i ∈ formula.vars, wires[i]? = some (assignment i)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux? (compileRaw available formula) wires = some result ∧
        result.size = wires.size + formula.size ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        result[rawOutputWire available formula]? = some (formula.eval assignment) :=
  evalAux?_compileRaw_of_agree_internal available formula assignment wires
    hsize hvars hagree

/-- Compiled formula evaluation appends exactly `formula.size` wires, preserves
the entire existing memo array, and puts the semantic value on the last new
wire. Every existing memo entry must realize the corresponding value of the
absolute-wire assignment. -/
theorem evalAux?_compileRaw (available : ℕ) [NeZero available]
    (formula : BoolFormula) (assignment : ℕ → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hinput : ∀ i < available, wires[i]? = some (assignment i))
    (hvars : ∀ i ∈ formula.vars, i < available) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux? (compileRaw available formula) wires = some result ∧
        result.size = wires.size + formula.size ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        result[rawOutputWire available formula]? = some (formula.eval assignment) :=
  evalAux?_compileRaw_internal available formula assignment wires hsize hinput hvars

end BoolFormula

end Complexity
