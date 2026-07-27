/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Batch.Internal

/-!
# Batch compilation of Boolean formulas

This module exposes finite Boolean-formula combinators and a batch compiler
that turns a list of formulas into appendable raw circuit syntax. Every source
formula is evaluated against the incoming prefix; a final copy phase places
all results in one contiguous block starting at `rawBatchOutputBase`.

## Main definitions and results

- `BoolFormula.literal`, `conjs`, and `disjs`: small formula constructors.
- `BoolFormula.compileRawOutputs`: sequential variable-sized compilation.
- `BoolFormula.compileRawBatch`: sequential compilation plus output packing.
- `BoolFormula.length_compileRawBatch`: exact gate count.
- `BoolFormula.topologicallyWellFormed_compileRawBatch`: backward references.
- `BoolFormula.evalAux?_compileRawBatch`: exact packed-output semantics.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

open CircuitCode

/-- A literal evaluates to whether its source wire has the requested value. -/
@[simp] theorem eval_literal (wire : ℕ) (value : Bool)
    (assignment : ℕ → Bool) :
    (literal wire value).eval assignment = decide (assignment wire = value) :=
  eval_literal_internal wire value assignment

/-- A literal requires at most two formula nodes. -/
theorem size_literal_le_two (wire : ℕ) (value : Bool) :
    (literal wire value).size ≤ 2 :=
  size_literal_le_two_internal wire value

/-- Finite conjunction evaluates as Boolean `List.all`. -/
@[simp] theorem eval_conjs (formulas : List BoolFormula)
    (assignment : ℕ → Bool) :
    (conjs formulas).eval assignment =
      formulas.all (fun formula => formula.eval assignment) :=
  eval_conjs_internal formulas assignment

/-- Finite disjunction evaluates as Boolean `List.any`. -/
@[simp] theorem eval_disjs (formulas : List BoolFormula)
    (assignment : ℕ → Bool) :
    (disjs formulas).eval assignment =
      formulas.any (fun formula => formula.eval assignment) :=
  eval_disjs_internal formulas assignment

/-- Exact tree size of a finite conjunction. -/
@[simp] theorem size_conjs (formulas : List BoolFormula) :
    (conjs formulas).size =
      1 + (formulas.map fun formula => formula.size + 1).sum :=
  size_conjs_internal formulas

/-- Exact tree size of a finite disjunction. -/
@[simp] theorem size_disjs (formulas : List BoolFormula) :
    (disjs formulas).size =
      1 + (formulas.map fun formula => formula.size + 1).sum :=
  size_disjs_internal formulas

/-- Sequential compilation emits the sum of the formula tree sizes. -/
@[simp] theorem length_compileRawOutputs_circuit (available : ℕ)
    (formulas : List BoolFormula) :
    (compileRawOutputs available formulas).circuit.length =
      (formulas.map size).sum :=
  length_compileRawOutputs_circuit_internal available formulas

/-- Sequential compilation records exactly one output per formula. -/
@[simp] theorem length_compileRawOutputs_outputs (available : ℕ)
    (formulas : List BoolFormula) :
    (compileRawOutputs available formulas).outputs.length = formulas.length :=
  length_compileRawOutputs_outputs_internal available formulas

/-- A packed batch emits every formula gate and one final copy per formula. -/
@[simp] theorem length_compileRawBatch (available : ℕ)
    (formulas : List BoolFormula) :
    (compileRawBatch available formulas).length =
      (formulas.map size).sum + formulas.length :=
  length_compileRawBatch_internal available formulas

/-- If every formula variable names an incoming wire, the entire packed batch
is topologically well formed. -/
theorem topologicallyWellFormed_compileRawBatch (available : ℕ)
    [NeZero available] (formulas : List BoolFormula)
    (hvars : ∀ formula ∈ formulas, ∀ i ∈ formula.vars, i < available) :
    (compileRawBatch available formulas).TopologicallyWellFormed available :=
  topologicallyWellFormed_compileRawBatch_internal available formulas hvars

/-- Batch evaluation preserves the incoming memo array and packs source
formula values into a contiguous final block, in source order. -/
theorem evalAux?_compileRawBatch (available : ℕ) [NeZero available]
    (formulas : List BoolFormula) (assignment : ℕ → Bool)
    (wires : Array Bool) (hsize : wires.size = available)
    (hinput : ∀ i < available, wires[i]? = some (assignment i))
    (hvars : ∀ formula ∈ formulas, ∀ i ∈ formula.vars, i < available) :
    ∃ result,
      RawCircuit.evalAux? (compileRawBatch available formulas) wires = some result ∧
        result.size =
          wires.size + (formulas.map size).sum + formulas.length ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        (∀ j : Fin formulas.length,
          result[rawBatchOutputBase available formulas + j.val]? =
            some ((formulas.get j).eval assignment)) :=
  evalAux?_compileRawBatch_internal available formulas assignment wires
    hsize hinput hvars

end BoolFormula

end Complexity
