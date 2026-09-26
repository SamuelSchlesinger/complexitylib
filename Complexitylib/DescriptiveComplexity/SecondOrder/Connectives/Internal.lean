/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Connectives.Defs

/-!
# Correctness of existential prefix merging

Moving a relation quantifier across an independent operand preserves truth.
Relation renaming prevents capture and preserves the matrices and their sizes.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem size_mergeExist_internal {V : Vocabulary} (isConjunction : Bool)
    {rctx : List Nat} {n : Nat} (φ ψ : SOFormula V rctx n) :
    (φ.mergeExist isConjunction ψ).size = φ.size + ψ.size + 1 := by
  fun_induction SOFormula.mergeExist isConjunction φ ψ <;> simp_all [SOFormula.size] <;> omega

private theorem matrix_of_existSO {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (h : φ.IsExistSO)
    (hn : ∀ k ψ, φ = SOFormula.soExist k ψ → False) : φ.IsFOMatrix := by
  cases φ <;> try exact h
  exact hn _ _ rfl

theorem isExistSO_mergeExist_internal {V : Vocabulary} (isConjunction : Bool)
    {rctx : List Nat} {n : Nat} (φ ψ : SOFormula V rctx n) :
    φ.IsExistSO → ψ.IsExistSO → (φ.mergeExist isConjunction ψ).IsExistSO := by
  fun_induction SOFormula.mergeExist isConjunction φ ψ with
  | case1 n rctx k φ ψ ih =>
    intro hφ hψ
    exact ih hφ ((SOFormula.isExistSO_renameRel _ _).mpr hψ)
  | case2 n rctx k ψ φ hn ih =>
    intro hφ hψ
    exact ih ((SOFormula.isExistSO_renameRel _ _).mpr hφ) hψ
  | case3 rctx n hb φ ψ hnφ hnψ =>
    intro hφ hψ
    exact ⟨matrix_of_existSO φ hφ hnφ, matrix_of_existSO ψ hψ hnψ⟩
  | case4 rctx n hb φ ψ hnφ hnψ =>
    intro hφ hψ
    exact ⟨matrix_of_existSO φ hφ hnφ, matrix_of_existSO ψ hψ hnψ⟩

theorem mergeExist_sat_internal {V : Vocabulary} (isConjunction : Bool)
    {rctx : List Nat} {n : Nat} (φ ψ : SOFormula V rctx n) (A : FinStruct V) :
    ∀ (σ : Env A.card n) (ρ : REnv A.card rctx),
      (φ.mergeExist isConjunction ψ).Sat A σ ρ ↔
        if isConjunction then φ.Sat A σ ρ ∧ ψ.Sat A σ ρ else φ.Sat A σ ρ ∨ ψ.Sat A σ ρ := by
  fun_induction SOFormula.mergeExist isConjunction φ ψ with
  | case1 n rctx k φ ψ ih =>
    intro σ ρ
    simp only [SOFormula.Sat, ih, SOFormula.renameRel_weaken_sat]
    cases isConjunction <;> simp [exists_or]
  | case2 n rctx k ψ φ hn ih =>
    intro σ ρ
    simp only [SOFormula.Sat, ih, SOFormula.renameRel_weaken_sat]
    cases isConjunction <;> simp [exists_or]
  | case3 rctx n hb φ ψ hnφ hnψ =>
    intro σ ρ
    simp [SOFormula.Sat, hb]
  | case4 rctx n hb φ ψ hnφ hnψ =>
    intro σ ρ
    simp [SOFormula.Sat, hb]

end Complexity.DescriptiveComplexity
