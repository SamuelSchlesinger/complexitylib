/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation
public import Complexitylib.Algebraic.Reduction

/-!
# Minimum-cost circuit realizations

A realization chooses one implementation circuit for each source operation.
This module minimizes those choices independently, turning pulled-back cost
into the intrinsic implementation cost of each operation rather than the cost
of an arbitrary selected gadget.
-/

@[expose] public section

namespace Algebraic

/-- The scalar target associated with one interpreted operation. -/
def _root_.Cslib.Circuits.Interpretation.operationTarget
    (interpretation : Interpretation σ U)
    (op : σ.Op) : Target U (σ.Arity op) 1 :=
  fun input _ => interpretation op input

export Cslib.Circuits (Interpretation.operationTarget)

namespace Realization

/-- Every operation circuit in a realization computes its source operation. -/
theorem operation_computes
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (op : σ.Op) :
    (realization.operation op).ComputesWith target
      (source.operationTarget op) := by
  intro input
  funext output
  rw [Fin.eq_zero output]
  exact realization.operation_eval op input

/-- Functional completeness supplies a realization of every interpreted
signature on the same carrier. The choice is classical, not executable. -/
noncomputable def ofFunctionalCompleteness
    (source : Interpretation σ U)
    (target : Interpretation τ U)
    (complete : target.FunctionallyComplete) :
    Realization σ τ source target := by
  classical
  let witness (op : σ.Op) :=
    complete (σ.Arity op) 1 (source.operationTarget op)
  let gateCount (op : σ.Op) := Classical.choose (witness op)
  let operation (op : σ.Op) : Circuit τ (σ.Arity op) (gateCount op) 1 :=
    Classical.choose (Classical.choose_spec (witness op))
  have computes (op : σ.Op) :
      (operation op).ComputesWith target (source.operationTarget op) :=
    Classical.choose_spec (Classical.choose_spec (witness op))
  exact
    { gateCount := gateCount
      operation := operation
      realizes := by
        funext op input
        exact congrFun (computes op input) 0 }

end Realization

/-- A realization whose selected implementation of every source operation is
minimum for the target cost model. -/
structure OptimalRealization
    (σ τ : Signature)
    (source : Interpretation σ U)
    (target : Interpretation τ U)
    (operationCost : OperationCost τ) extends
      Realization σ τ source target where
  /-- Each selected operation circuit has minimum target cost. -/
  optimal : ∀ op,
    (operation op).CostMinimal operationCost target
      (source.operationTarget op)

namespace Realization

/-- Replace every selected operation gadget by a minimum-cost implementation.
Ties are broken by internal gate count through `Circuit.minimum`. -/
noncomputable def minimize
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (operationCost : OperationCost τ) :
    OptimalRealization σ τ source target operationCost := by
  classical
  let selected (op : σ.Op) :=
    (realization.operation op).minimum operationCost target
      (source.operationTarget op) (realization.operation_computes op)
  exact
    { toRealization :=
        { gateCount := fun op => (selected op).gateCount
          operation := fun op => (selected op).circuit
          realizes := by
            funext op input
            exact congrFun ((selected op).computes input) 0 }
      optimal := fun op => (selected op).minimal.cost }

/-- The intrinsic implementation cost obtained by minimizing the realization's
gadgets. Its value is independent of the initial realization. -/
noncomputable def minimumCost
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization : Realization σ τ source target)
    (operationCost : OperationCost τ) : OperationCost σ :=
  (realization.minimize operationCost).toRealization.pullCost operationCost

end Realization

namespace OptimalRealization

/-- An optimal realization charges no more for an operation than any other
realization of the same interpreted signatures. -/
theorem pullCost_le
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    {operationCost : OperationCost τ}
    (optimal : OptimalRealization σ τ source target operationCost)
    (competitor : Realization σ τ source target)
    (op : σ.Op) :
    optimal.toRealization.pullCost operationCost op ≤
      competitor.pullCost operationCost op := by
  exact optimal.optimal op (competitor.operation op)
    (competitor.operation_computes op)

/-- Any two optimal realizations induce exactly the same source cost model. -/
theorem pullCost_eq
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    {operationCost : OperationCost τ}
    (left right : OptimalRealization σ τ source target operationCost) :
    left.toRealization.pullCost operationCost =
      right.toRealization.pullCost operationCost := by
  funext op
  exact Nat.le_antisymm (left.pullCost_le right.toRealization op)
    (right.pullCost_le left.toRealization op)

end OptimalRealization

namespace Realization

/-- Intrinsic operation cost is bounded by the cost pulled back through any
chosen realization. -/
theorem minimumCost_le
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (realization competitor : Realization σ τ source target)
    (operationCost : OperationCost τ)
    (op : σ.Op) :
    realization.minimumCost operationCost op ≤
      competitor.pullCost operationCost op :=
  (realization.minimize operationCost).pullCost_le competitor op

/-- Intrinsic minimum cost does not depend on the initial realization used to
establish implementability. -/
theorem minimumCost_congr
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    (left right : Realization σ τ source target)
    (operationCost : OperationCost τ) :
    left.minimumCost operationCost = right.minimumCost operationCost :=
  (left.minimize operationCost).pullCost_eq
    (right.minimize operationCost)

/-- Minimizing an already optimal realization recovers the same intrinsic cost
model. -/
theorem minimumCost_eq
    {source : Interpretation σ U}
    {target : Interpretation τ U}
    {operationCost : OperationCost τ}
    (optimal : OptimalRealization σ τ source target operationCost) :
    optimal.toRealization.minimumCost operationCost =
      optimal.toRealization.pullCost operationCost :=
  (optimal.toRealization.minimize operationCost).pullCost_eq optimal

end Realization

end Algebraic
