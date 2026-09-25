/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Wiring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Enumerating nonuniform affine offsets

All direction/scalar products in a fixed candidate menu can be computed
offline. Adding a fixed offset to a binary vector then needs at most one
negation per bit. This circuit emits every translated point with a cost
linear in the total number of point bits.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.ConstantTranslations

open scoped BigOperators

/-- XOR with a hardwired bit uses either a wire or one negation. -/
def expression (offset : Bool) (source : DeMorgan.Wiring inputs) : DeMorgan.Expression inputs :=
  if offset then .not source.expression else source.expression

/-- Exact Boolean translation by a constant offset bit. -/
theorem expression_eval (offset : Bool) (source : DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) :
    (expression offset source).eval input = ((source.eval input) ^^ offset) := by
  cases offset <;> simp [expression, DeMorgan.Expression.eval]

/-- At most one charged gate per translated bit. -/
theorem expression_cost_le (offset : Bool) (source : DeMorgan.Wiring inputs) :
    (expression offset source).standardCost ≤ 1 := by
  cases offset <;> simp [expression, DeMorgan.Expression.standardCost]

/-- Emit all translated points, sharing the source wires freely. -/
def circuit (offsets : Fin points → Fin width → Bool)
    (sources : Fin points → Fin width → DeMorgan.Wiring inputs) :=
  Circuit.parallelFin (points * width)
    (fun output =>
      let pair := (finProdFinEquiv (m := points) (n := width)).symm output
      (expression (offsets pair.1 pair.2) (sources pair.1 pair.2)).gateCount)
    (fun output =>
      let pair := (finProdFinEquiv (m := points) (n := width)).symm output
      (expression (offsets pair.1 pair.2) (sources pair.1 pair.2)).circuit)

/-- Each output point is its source vector XOR its fixed offset. -/
theorem circuit_eval (offsets : Fin points → Fin width → Bool)
    (sources : Fin points → Fin width → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (point : Fin points) (bit : Fin width) :
    (circuit offsets sources).eval DeMorgan.interpretation input (finProdFinEquiv (point, bit)) =
      ((sources point bit).eval input ^^ offsets point bit) := by
  rw [circuit, Circuit.eval_parallelFin]
  simp only [Equiv.symm_apply_apply, DeMorgan.Expression.circuit_eval, expression_eval]

/-- The whole point generator costs at most its number of output bits. -/
theorem circuit_cost_le (offsets : Fin points → Fin width → Bool)
    (sources : Fin points → Fin width → DeMorgan.Wiring inputs) :
    (circuit offsets sources).cost DeMorgan.standardCost ≤ points * width := by
  rw [circuit, Circuit.cost_parallelFin]
  calc
    _ ≤ ∑ _ : Fin (points * width), 1 := by
      apply Finset.sum_le_sum
      intro output _
      rw [DeMorgan.Expression.circuit_cost]
      exact expression_cost_le _ _
    _ = _ := by simp

end Algebraic.MassProduction.Nonuniform.ConstantTranslations
