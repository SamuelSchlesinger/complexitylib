/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Family.Defs

/-!
# Semantics-preserving maps between circuit bases -- definitions

A `Basis.Hom B₁ B₂` maps every operation-and-arity pair of `B₁` to a `B₂`
operation that accepts that arity and has exactly the same Boolean semantics.
The target label may depend on arity: for example, an unbounded AND of fan-in
`n` maps to the threshold operation "at least `n`." The map changes only gate
labels; fan-in, wiring, negation flags, gate count, and circuit topology are
preserved exactly.
-/

@[expose] public section

namespace Complexity

/-- A semantics-preserving operation map between Boolean bases. -/
structure Basis.Hom (source target : Basis) where
  /-- Translate a source operation at a specified gate arity. -/
  mapOp : source.Op → ℕ → target.Op
  /-- Every legal source arity is legal for the translated operation. -/
  mapArity : ∀ (op : source.Op) (n : ℕ),
    (source.arity op).satisfiedBy n →
      (target.arity (mapOp op n)).satisfiedBy n
  /-- Operation translation preserves semantics exactly. -/
  eval_map : ∀ (op : source.Op) (n : ℕ)
    (arityOk : (source.arity op).satisfiedBy n)
    (inputs : BitString n),
    target.eval (mapOp op n) n (mapArity op n arityOk) inputs =
      source.eval op n arityOk inputs

namespace Gate

/-- Relabel a gate along a basis homomorphism without changing its topology. -/
def mapBasis (hom : Basis.Hom source target)
    (gate : Gate source W) : Gate target W where
  op := hom.mapOp gate.op gate.fanIn
  fanIn := gate.fanIn
  arityOk := hom.mapArity gate.op gate.fanIn gate.arityOk
  inputs := gate.inputs
  negated := gate.negated

end Gate

namespace Circuit

/-- Relabel every gate of a circuit along a basis homomorphism. -/
def mapBasis [NeZero N] [NeZero M]
    (hom : Basis.Hom source target)
    (circuit : Circuit source N M G) :
    Circuit target N M G where
  gates := fun index => (circuit.gates index).mapBasis hom
  outputs := fun index => (circuit.outputs index).mapBasis hom
  acyclic := by
    intro index input
    exact circuit.acyclic index input

end Circuit

namespace CircuitFamily

/-- Relabel every positive-length circuit in a nonuniform family. -/
def mapBasis (hom : Basis.Hom source target)
    (family : CircuitFamily source) :
    CircuitFamily target where
  emptyOutput := family.emptyOutput
  circuits := fun n =>
    ⟨family.internalGateCount n,
      (family.circuit n).mapBasis hom⟩

end CircuitFamily
end Complexity
