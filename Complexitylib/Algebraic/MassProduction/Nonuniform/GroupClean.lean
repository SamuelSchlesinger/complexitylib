/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression

/-!
# Aggregating point conflicts into clean requests

A request is clean when none of its point slots has a conflict. The shared
point-conflict circuit runs once; each request adds one OR per slot and one
negation. Slot counts may be zero, in which case every request is clean.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GroupClean

open scoped BigOperators

/-- A clean request is the negation of the OR of all its point conflicts. -/
def expression (points : Fin slots → Fin pointCount) : DeMorgan.Expression pointCount :=
  .not (DeMorgan.Expression.finOr slots (fun slot => .input (points slot)))

/-- Compile one clean flag per request. -/
def flagsCircuit (points : Fin requests → Fin slots → Fin pointCount) :=
  Circuit.parallelFin requests
    (fun request => (expression (points request)).circuit)

/-- No point in a request is conflicting exactly when its clean flag is true. -/
theorem flagsCircuit_eval_iff
    (points : Fin requests → Fin slots → Fin pointCount)
    (input : Fin pointCount → Bool) (request : Fin requests) :
    (flagsCircuit points).eval DeMorgan.interpretation input request = true ↔
      ∀ slot, input (points request slot) = false := by
  rw [flagsCircuit, Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval]
  simp only [expression, DeMorgan.Expression.eval, Bool.not_eq_true',
    DeMorgan.Expression.finOr_eval]
  exact (Bool.eq_false_iff.trans (not_congr
    (DeMorgan.Expression.finOrValue_eq_true_iff slots (fun slot => input (points request slot))))).trans
      (by simp only [not_exists, Bool.eq_false_iff])

/-- Exactly one OR gate per slot and one negation per request. -/
theorem flagsCircuit_cost
    (points : Fin requests → Fin slots → Fin pointCount) :
    (flagsCircuit points).cost DeMorgan.standardCost = requests * (slots + 1) := by
  rw [flagsCircuit, Circuit.cost_parallelFin]
  simp [DeMorgan.Expression.circuit_cost, expression, DeMorgan.Expression.standardCost,
    DeMorgan.Expression.finOr_standardCost]

/-- Aggregate all requests after running the point circuit once. -/
def circuit (points : Fin requests → Fin slots → Fin pointCount)
    (conflicts : Circuit DeMorgan.signature inputs pointCount) :=
  (flagsCircuit points).comp conflicts

/-- Exact clean-request semantics for a shared point-conflict circuit. -/
theorem circuit_eval_iff
    (points : Fin requests → Fin slots → Fin pointCount)
    (conflicts : Circuit DeMorgan.signature inputs pointCount)
    (input : Fin inputs → Bool) (request : Fin requests) :
    (circuit points conflicts).eval DeMorgan.interpretation input request = true ↔
      ∀ slot, conflicts.eval DeMorgan.interpretation input (points request slot) = false := by
  rw [circuit, Circuit.eval_comp, flagsCircuit_eval_iff]

/-- Only linear work in the number of request-point slots is added. -/
theorem circuit_cost
    (points : Fin requests → Fin slots → Fin pointCount)
    (conflicts : Circuit DeMorgan.signature inputs pointCount) :
    (circuit points conflicts).cost DeMorgan.standardCost =
      conflicts.cost DeMorgan.standardCost + requests * (slots + 1) := by
  rw [circuit, Circuit.cost_comp, flagsCircuit_cost]

end Algebraic.MassProduction.Nonuniform.GroupClean
