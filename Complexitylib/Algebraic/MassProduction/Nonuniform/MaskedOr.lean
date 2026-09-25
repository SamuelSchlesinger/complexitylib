/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression

/-!
# Combining shared point flags

Compute `valid AND (collision OR occupied)` once per point. The two arrays
of collision flags and occupancy flags, and the validity array, are supplied
as shared subcircuits; their costs are each charged once.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.MaskedOr

open scoped BigOperators

/-- Two Boolean operations combine the three flags of one point. -/
def expression (index : Fin count) : DeMorgan.Expression ((count + count) + count) :=
  .and (.input (Fin.natAdd (count + count) index))
    (.or (.input (Fin.castAdd count (Fin.castAdd count index)))
      (.input (Fin.castAdd count (Fin.natAdd count index))))

/-- Compile one constant-size expression per point. -/
def combineCircuit (count : Nat) :=
  Circuit.parallelFin count (fun index => (expression index).gateCount)
    (fun index => (expression index).circuit)

/-- The combining stage reads the corresponding bits of each shared array. -/
theorem combineCircuit_eval
    (left right valid : Fin count → Bool) (index : Fin count) :
    (combineCircuit count).eval DeMorgan.interpretation
      (Fin.append (Fin.append left right) valid) index =
        (valid index && (left index || right index)) := by
  rw [combineCircuit, Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]
  simp only [expression, DeMorgan.Expression.eval, Fin.append_left, Fin.append_right]

/-- Combining costs exactly two gates per point. -/
theorem combineCircuit_cost :
    (combineCircuit count).cost DeMorgan.standardCost = 2 * count := by
  rw [combineCircuit, Circuit.cost_parallelFin]
  simp [DeMorgan.Expression.circuit_cost, expression, DeMorgan.Expression.standardCost, Nat.mul_comm]

/-- Evaluate each shared subcircuit once and combine their pointwise outputs. -/
def circuit
    (left : Circuit DeMorgan.signature inputs leftGates count)
    (right : Circuit DeMorgan.signature inputs rightGates count)
    (valid : Circuit DeMorgan.signature inputs validGates count) :=
  (combineCircuit count).comp ((left.parallel right).parallel valid)

/-- Exact pointwise semantics of the shared composition. -/
theorem circuit_eval
    (left : Circuit DeMorgan.signature inputs leftGates count)
    (right : Circuit DeMorgan.signature inputs rightGates count)
    (valid : Circuit DeMorgan.signature inputs validGates count)
    (input : Fin inputs → Bool) (index : Fin count) :
    (circuit left right valid).eval DeMorgan.interpretation input index =
      (valid.eval DeMorgan.interpretation input index &&
        (left.eval DeMorgan.interpretation input index || right.eval DeMorgan.interpretation input index)) := by
  rw [circuit, Circuit.eval_comp, Circuit.eval_parallel, Circuit.eval_parallel, combineCircuit_eval]

/-- Each shared subcircuit is charged once, plus two gates per point. -/
theorem circuit_cost
    (left : Circuit DeMorgan.signature inputs leftGates count)
    (right : Circuit DeMorgan.signature inputs rightGates count)
    (valid : Circuit DeMorgan.signature inputs validGates count) :
    (circuit left right valid).cost DeMorgan.standardCost =
      (left.cost DeMorgan.standardCost + right.cost DeMorgan.standardCost +
        valid.cost DeMorgan.standardCost) + 2 * count := by
  rw [circuit, Circuit.cost_comp, Circuit.cost_parallel, Circuit.cost_parallel, combineCircuit_cost]

end Algebraic.MassProduction.Nonuniform.MaskedOr
