/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.EssentialInput
public import Complexitylib.Circuits.Monotone.Defs

/-!
# Monotone Boolean formulas -- proof internals
-/

@[expose] public section

namespace Complexity
namespace MonotoneFormula

theorem eval_toBoolFormula_internal (formula : MonotoneFormula N)
    (input : BitString N) :
    formula.toBoolFormula.eval input.toTotal = formula.eval input := by
  induction formula <;>
    simp_all [toBoolFormula, eval, BoolFormula.eval]

theorem size_toBoolFormula_internal (formula : MonotoneFormula N) :
    formula.toBoolFormula.size = formula.size := by
  induction formula <;>
    simp_all [toBoolFormula, size, BoolFormula.size]

theorem leaves_toBoolFormula_internal (formula : MonotoneFormula N) :
    formula.toBoolFormula.leaves = formula.leaves := by
  induction formula <;>
    simp_all [toBoolFormula, leaves, BoolFormula.leaves]

theorem depth_toBoolFormula_internal (formula : MonotoneFormula N) :
    formula.toBoolFormula.depth = formula.depth := by
  induction formula <;>
    simp_all [toBoolFormula, depth, BoolFormula.depth]

theorem eval_monotone_internal (formula : MonotoneFormula N) :
    IsMonotoneBoolFun formula.eval := by
  unfold IsMonotoneBoolFun
  induction formula <;>
    aesop (add simp [eval, BitString.PointwiseLE])

theorem eval_eq_of_agree_internal (formula : MonotoneFormula N)
    {x y : BitString N}
    (agree : ∀ index ∈ formula.vars, x index = y index) :
    formula.eval x = formula.eval y := by
  induction formula with
  | var index =>
      exact agree index (Finset.mem_singleton_self index)
  | conj left right ihLeft ihRight =>
      simp only [eval]
      rw [ihLeft (fun index h => agree index
        (Finset.mem_union_left _ h))]
      rw [ihRight (fun index h => agree index
        (Finset.mem_union_right _ h))]
  | disj left right ihLeft ihRight =>
      simp only [eval]
      rw [ihLeft (fun index h => agree index
        (Finset.mem_union_left _ h))]
      rw [ihRight (fun index h => agree index
        (Finset.mem_union_right _ h))]

theorem card_vars_le_leaves_internal (formula : MonotoneFormula N) :
    formula.vars.card ≤ formula.leaves := by
  induction formula with
  | var index => simp [vars, leaves]
  | conj left right ihLeft ihRight =>
      simp only [vars, leaves]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add ihLeft ihRight)
  | disj left right ihLeft ihRight =>
      simp only [vars, leaves]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add ihLeft ihRight)

theorem leaves_le_two_pow_depth_internal (formula : MonotoneFormula N) :
    formula.leaves ≤ 2 ^ formula.depth := by
  rw [← leaves_toBoolFormula_internal,
    ← depth_toBoolFormula_internal]
  exact BoolFormula.leaves_le_two_pow_depth formula.toBoolFormula

theorem essentialInputs_subset_vars_internal
    (formula : MonotoneFormula N) :
    essentialInputs (fun input (_ : Fin 1) => formula.eval input) ⊆
      formula.vars := by
  intro index hessential
  by_contra hmissing
  simp only [essentialInputs, Finset.mem_filter] at hessential
  rcases hessential.2 with ⟨input, hchange⟩
  apply hchange
  funext output
  apply eval_eq_of_agree_internal
  intro queried hqueried
  have hne : queried ≠ index := by
    intro heq
    subst queried
    exact hmissing hqueried
  simp [hne]

theorem card_essentialInputs_le_leaves_internal
    (formula : MonotoneFormula N) :
    (essentialInputs
      (fun input (_ : Fin 1) => formula.eval input)).card ≤
        formula.leaves := by
  exact (Finset.card_le_card
    (essentialInputs_subset_vars_internal formula)).trans
      (card_vars_le_leaves_internal formula)

theorem card_essentialInputs_le_leaves_of_computes_internal
    (formula : MonotoneFormula N) (function : BitString N → Bool)
    (computes : formula.Computes function) :
    (essentialInputs (fun input (_ : Fin 1) => function input)).card ≤
      formula.leaves := by
  have hfunctions :
      (fun input (_ : Fin 1) => function input) =
        (fun input (_ : Fin 1) => formula.eval input) := by
    funext input output
    exact (computes input).symm
  rw [hfunctions]
  exact card_essentialInputs_le_leaves_internal formula

end MonotoneFormula
end Complexity
