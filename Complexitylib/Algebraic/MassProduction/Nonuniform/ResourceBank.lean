/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Parallel
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# One evaluation circuit per resource

The bank is indexed by the exact resource count, so padding used by routing
does not increase the leading evaluation cost. Each member reads its own
suffix block and produces one Boolean value.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.ResourceBank

variable {resources : Nat}

/-- Evaluate every resource once on its own input block. -/
def circuit (members : (resource : Fin resources) → Circuit DeMorgan.signature suffixWidth 1) :=
  Circuit.parallelFin resources
    (fun resource => (members resource).mapInputs (fun bit => finProdFinEquiv (resource, bit)))

/-- Every bank output is exactly its resource's evaluation on its suffix block. -/
theorem circuit_eval
    (members : (resource : Fin resources) → Circuit DeMorgan.signature suffixWidth 1)
    (input : Fin (resources * suffixWidth) → Bool) (resource : Fin resources) :
    (circuit members).eval DeMorgan.interpretation input resource =
      (members resource).eval DeMorgan.interpretation
        (fun bit => input (finProdFinEquiv (resource, bit))) 0 := by
  rw [circuit, Circuit.eval_parallelFin, Circuit.eval_mapInputs]
  rfl

/-- No routing padding is charged as an extra resource evaluation. -/
theorem circuit_cost
    (members : (resource : Fin resources) → Circuit DeMorgan.signature suffixWidth 1) :
    (circuit members).cost DeMorgan.standardCost = ∑ resource, (members resource).cost DeMorgan.standardCost := by
  rw [circuit, Circuit.cost_parallelFin]
  simp only [Circuit.cost_mapInputs]

/-- A common resource bound contributes exactly `resources * bound`. -/
theorem circuit_cost_le
    (members : (resource : Fin resources) → Circuit DeMorgan.signature suffixWidth 1)
    (bounded : ∀ resource, (members resource).cost DeMorgan.standardCost ≤ bound) :
    (circuit members).cost DeMorgan.standardCost ≤ resources * bound := by
  rw [circuit_cost]
  calc
    _ ≤ ∑ _resource : Fin resources, bound := Finset.sum_le_sum (fun resource _ => bounded resource)
    _ = _ := by simp

end Algebraic.MassProduction.Nonuniform.ResourceBank
