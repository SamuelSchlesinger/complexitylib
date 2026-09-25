/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MenuPointLayout
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GroupClean

/-!
# Circuit evaluation of every candidate's clean requests

Shared point-conflict detection followed by one finite OR per request returns
the exact clean-request predicate for every candidate. The cost includes one
occupancy router for the whole menu and is linear in the number of point
records up to polynomial width and sorting-depth factors.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.MenuClean

open Sorting

set_option backward.isDefEq.respectTransparency false

/-- Point slots of the request at a row-major candidate-request position. -/
def pointIndices (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (line : Fin (candidates * requests)) (slot : Fin slots) : Fin (networkRecords depth) :=
  let pair := (finProdFinEquiv (m := candidates) (n := requests)).symm line
  layout (pair.1, pair.2, slot)

/-- The complete menu clean-flag circuit, before choosing a successful row. -/
noncomputable def circuit
    (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (codes : Fin candidates → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth) :=
  GroupClean.circuit (pointIndices layout)
    (PointConflicts.circuit (MenuPointLayout.groups layout codes) valid keys sourceKeys sourceFlags recordCount)

/-- Every fixed output is exactly its candidate's clean-request predicate. -/
theorem circuit_eval_iff
    (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (codes : Fin candidates → Fin groupWidth → Bool) (codesInjective : Function.Injective codes)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth)
    (input : Fin inputs → Bool) (candidate : Fin candidates) (request : Fin requests)
    (withinRequest : ∀ request left right,
      (valid (layout (candidate, request, left))).eval input = true →
      (valid (layout (candidate, request, right))).eval input = true →
      (fun bit => (keys (layout (candidate, request, left)) bit).eval input) =
        (fun bit => (keys (layout (candidate, request, right)) bit).eval input) → left = right) :
    (circuit layout codes valid keys sourceKeys sourceFlags recordCount).eval
      DeMorgan.interpretation input (finProdFinEquiv (candidate, request)) = true ↔
      Clean (fun request (_ : Unit) => EnumeratedClean.pointSet
        (fun slot => (valid (layout (candidate, request, slot))).eval input)
        (fun slot bit => (keys (layout (candidate, request, slot)) bit).eval input))
        (MenuPointLayout.occupied sourceKeys sourceFlags input) (fun _ => ()) request := by
  rw [circuit, GroupClean.circuit_eval_iff]
  simp only [pointIndices, Equiv.symm_apply_apply]
  calc
    _ ↔ ∀ slot, ¬ EnumeratedClean.Conflict
        (fun request slot => (valid (layout (candidate, request, slot))).eval input)
        (fun request slot bit => (keys (layout (candidate, request, slot)) bit).eval input)
        (MenuPointLayout.occupied sourceKeys sourceFlags input) request slot := by
      apply forall_congr'
      intro slot
      exact Bool.eq_false_iff.trans (not_congr
        (MenuPointLayout.pointCircuit_eval_iff layout codes codesInjective valid keys
          sourceKeys sourceFlags recordCount input candidate request slot))
    _ ↔ _ := EnumeratedClean.noConflict_iff_clean _ _ _ withinRequest request

/-- Explicit cost: one duplicate detector, one shared occupancy router,
two combining gates per point, and one aggregation per request. -/
theorem circuit_cost_le
    (layout : (Fin candidates × Fin requests × Fin slots) ≃ Fin (networkRecords depth))
    (codes : Fin candidates → Fin groupWidth → Bool)
    (valid : Fin (networkRecords depth) → DeMorgan.Wiring inputs)
    (keys : Fin (networkRecords depth) → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords depth + padding = networkRecords routingDepth) :
    (circuit layout codes valid keys sourceKeys sourceFlags recordCount).cost DeMorgan.standardCost ≤
      ((256 * networkRecords depth * (depth + (groupWidth + (1 + keyWidth)) + 1) ^ 5 +
        128 * networkRecords routingDepth * (routingDepth + keyWidth + 1 + 2) ^ 5) +
        2 * networkRecords depth) + (candidates * requests) * (slots + 1) := by
  rw [circuit, GroupClean.circuit_cost]
  exact Nat.add_le_add_right (PointConflicts.circuit_cost_le _ _ _ _ _ recordCount) _

end Algebraic.MassProduction.Nonuniform.MenuClean
