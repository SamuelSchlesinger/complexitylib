/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.NormalForm.Defs
public import Complexitylib.Circuits.Composition.Defs

/-!
# Leaf and connective circuits for unbounded formula compilation

Constants, literals, and unbounded connectives each use one output gate and no
internal gates. Literal negation uses the circuit model's free edge flags.
-/

@[expose] public section

namespace Complexity.AC0Formula

variable {N : Nat} [NeZero N]

/-- A nullary AND or OR gate computes a Boolean constant. -/
def constantCircuit (value : Bool) : Circuit Basis.unboundedAndOr N 1 0 where
  gates := Fin.elim0
  outputs _ :=
    { op := if value then .and else .or
      fanIn := 0
      arityOk := by cases value <;> trivial
      inputs := Fin.elim0
      negated := Fin.elim0 }
  acyclic i := i.elim0

/-- A unary AND gate with an edge flag computes a signed literal. -/
def literalCircuit (literal : Literal N) : Circuit Basis.unboundedAndOr N 1 0 where
  gates := Fin.elim0
  outputs _ :=
    { op := .and
      fanIn := 1
      arityOk := trivial
      inputs := fun _ => ⟨literal.var.val, by omega⟩
      negated := fun _ => !literal.polarity }
  acyclic i := i.elim0

/-- One unbounded gate combines all primary inputs by AND or OR. -/
def connectiveCircuit (op : AndOrOp) : Circuit Basis.unboundedAndOr N 1 0 where
  gates := Fin.elim0
  outputs _ :=
    { op := op
      fanIn := N
      arityOk := by cases op <;> trivial
      inputs := fun i => ⟨i.val, by omega⟩
      negated := fun _ => false }
  acyclic i := i.elim0

end Complexity.AC0Formula
