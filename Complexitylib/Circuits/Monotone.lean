/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Monotone.Defs
public import Complexitylib.Circuits.Monotone.Internal

/-!
# Monotone Boolean formulas

`MonotoneFormula N` is a typed formula tree over `N` variables using only
conjunction and disjunction. Its syntax makes monotonicity structural rather
than a side condition on a formula with negations.

The public results prove exact compatibility with `BoolFormula`, semantic
monotonicity, locality, and two elementary lower bounds: distinct variables
and essential variables are both bounded by the number of formula leaves.
-/

@[expose] public section

namespace Complexity
namespace MonotoneFormula

/-- Erasing finite-index proofs preserves evaluation. -/
theorem eval_toBoolFormula (formula : MonotoneFormula N)
    (input : BitString N) :
    formula.toBoolFormula.eval input.toTotal = formula.eval input :=
  eval_toBoolFormula_internal formula input

/-- Erasing finite-index proofs preserves total tree size. -/
theorem size_toBoolFormula (formula : MonotoneFormula N) :
    formula.toBoolFormula.size = formula.size :=
  size_toBoolFormula_internal formula

/-- Erasing finite-index proofs preserves the leaf count. -/
theorem leaves_toBoolFormula (formula : MonotoneFormula N) :
    formula.toBoolFormula.leaves = formula.leaves :=
  leaves_toBoolFormula_internal formula

/-- Erasing finite-index proofs preserves depth. -/
theorem depth_toBoolFormula (formula : MonotoneFormula N) :
    formula.toBoolFormula.depth = formula.depth :=
  depth_toBoolFormula_internal formula

/-- Every formula in the structurally monotone syntax computes a monotone
Boolean function. -/
theorem eval_monotone (formula : MonotoneFormula N) :
    IsMonotoneBoolFun formula.eval :=
  eval_monotone_internal formula

/-- Evaluation depends only on variables that occur in the formula. -/
theorem eval_eq_of_agree (formula : MonotoneFormula N)
    {x y : BitString N}
    (agree : ∀ index ∈ formula.vars, x index = y index) :
    formula.eval x = formula.eval y :=
  eval_eq_of_agree_internal formula agree

/-- The number of distinct variables is at most the number of leaves. -/
theorem card_vars_le_leaves (formula : MonotoneFormula N) :
    formula.vars.card ≤ formula.leaves :=
  card_vars_le_leaves_internal formula

/-- A depth-`d` binary formula has at most `2 ^ d` leaves. -/
theorem leaves_le_two_pow_depth (formula : MonotoneFormula N) :
    formula.leaves ≤ 2 ^ formula.depth :=
  leaves_le_two_pow_depth_internal formula

/-- Every essential input of the computed one-bit function occurs in the
formula. -/
theorem essentialInputs_subset_vars (formula : MonotoneFormula N) :
    essentialInputs (fun input (_ : Fin 1) => formula.eval input) ⊆
      formula.vars :=
  essentialInputs_subset_vars_internal formula

/-- The number of essential inputs is at most the formula's leaf count. -/
theorem card_essentialInputs_le_leaves (formula : MonotoneFormula N) :
    (essentialInputs
      (fun input (_ : Fin 1) => formula.eval input)).card ≤
        formula.leaves :=
  card_essentialInputs_le_leaves_internal formula

/-- A formula computing `function` needs at least one leaf per essential input
of `function`. -/
theorem card_essentialInputs_le_leaves_of_computes
    (formula : MonotoneFormula N) (function : BitString N → Bool)
    (computes : formula.Computes function) :
    (essentialInputs (fun input (_ : Fin 1) => function input)).card ≤
      formula.leaves :=
  card_essentialInputs_le_leaves_of_computes_internal formula function computes

end MonotoneFormula
end Complexity
