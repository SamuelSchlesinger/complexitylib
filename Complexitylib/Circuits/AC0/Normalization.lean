/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AC0.NormalForm
public import Complexitylib.Circuits.AC0.Normalization.Defs
public import Complexitylib.Circuits.AC0.Normalization.Internal

/-!
# AC0 circuit normalization

Every selected output of an unbounded AND/OR circuit unfolds to an equivalent
negation-normal unbounded formula. Duplicate signed inputs are removed before
unfolding, so the formula has:

* depth no larger than the selected circuit-output depth; and
* tree size at most `(2 * (N + G) + 1) ^ (outputDepth + 1)`.

For constant-depth, polynomial-gate circuit families this bound is polynomial.
No uniformity assumption is used.
-/

@[expose] public section

namespace Complexity

/-- A gate has at most two distinct signed occurrences of each available
source wire, regardless of how many duplicate incidences its raw input table
contains. -/
theorem Gate.signedSupport_card_le
    (gate : Gate Basis.unboundedAndOr W) (outerNegated : Bool) :
    (gate.signedSupport outerNegated).card ≤ 2 * W :=
  signedSupport_card_le_internal gate outerNegated

namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

/-- Wire normalization preserves semantics, including an optional requested
complement. -/
theorem eval_wireAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (input : BitString N) (negated : Bool)
    (wire : Fin (N + G)) :
    (circuit.wireAC0Formula negated wire).eval input =
      negated.xor (circuit.wireValue input wire) :=
  eval_wireAC0Formula_internal circuit input negated wire

/-- Output normalization preserves the selected output bit exactly. -/
theorem eval_outputAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (input : BitString N) (output : Fin M) :
    (circuit.outputAC0Formula output).eval input =
      circuit.eval input output :=
  eval_outputAC0Formula_internal circuit input output

/-- Normalizing a wire does not increase its circuit depth. -/
theorem depth_wireAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (negated : Bool) (wire : Fin (N + G)) :
    (circuit.wireAC0Formula negated wire).depth ≤
      circuit.wireDepth wire :=
  depth_wireAC0Formula_internal circuit negated wire

/-- Normalizing an output does not increase its output depth. -/
theorem depth_outputAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (output : Fin M) :
    (circuit.outputAC0Formula output).depth ≤
      circuit.outputDepth output :=
  depth_outputAC0Formula_internal circuit output

/-- The normalized formula below a wire has an explicit tree-size bound in
terms of the number of available signed wires and wire depth. -/
theorem size_wireAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (negated : Bool) (wire : Fin (N + G)) :
    (circuit.wireAC0Formula negated wire).size ≤
      (2 * (N + G) + 1) ^ (circuit.wireDepth wire + 1) :=
  size_wireAC0Formula_internal circuit negated wire

/-- The normalized selected-output formula has polynomial tree size whenever
gate count is polynomial and depth is constant. -/
theorem size_outputAC0Formula
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (output : Fin M) :
    (circuit.outputAC0Formula output).size ≤
      (2 * (N + G) + 1) ^ (circuit.outputDepth output + 1) :=
  size_outputAC0Formula_internal circuit output

/-- Bundled finite AC0 normalization theorem. -/
theorem outputAC0Formula_spec
    (circuit : Circuit Basis.unboundedAndOr N M G)
    (output : Fin M) :
    (∀ input,
      (circuit.outputAC0Formula output).eval input =
        circuit.eval input output) ∧
      (circuit.outputAC0Formula output).depth ≤
        circuit.outputDepth output ∧
      (circuit.outputAC0Formula output).size ≤
        (2 * (N + G) + 1) ^ (circuit.outputDepth output + 1) :=
  ⟨fun input => eval_outputAC0Formula circuit input output,
    depth_outputAC0Formula circuit output,
    size_outputAC0Formula circuit output⟩

end Circuit
end Complexity
