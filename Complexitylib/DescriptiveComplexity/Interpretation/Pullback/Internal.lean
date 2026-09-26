/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation.Pullback.Defs

/-!
# Correctness of tagged formula pullback

The semantic induction uses coordinate evaluation and compatibility with tuple
binders. Equality compares both the tag and every coordinate. Quantifiers range
over the full tagged tuple universe, using `elementEquiv` to transfer witnesses.
-/

public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim n m : Nat}

theorem termCoords_eval (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V)
    (τ : Fin n → Fin tags) (κ : Fin n → Fin dim → Term V m) (σ : Env A.card m)
    (t : Term W n) :
    elementEquiv A.card tags dim (t.eval (I.apply A) (coordEnv A τ κ σ)) =
      (I.termTag τ t, fun j => (I.termCoords κ t j).eval A σ) := by
  cases t <;> simp [Term.eval, coordEnv, termTag, termCoords]

theorem coordEnv_lift (A : FinStruct V) (τ : Fin n → Fin tags)
    (κ : Fin n → Fin dim → Term V m) (σ : Env A.card m)
    (tag : Fin tags) (v : Env A.card dim) :
    coordEnv A (Fin.cons tag τ) (liftCoords κ) (envBlock σ v) =
      envCons ((elementEquiv A.card tags dim).symm (tag, v)) (coordEnv A τ κ σ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [coordEnv, liftCoords, Term.eval, envBlock_new, envCons]
  | succ i => simp [coordEnv, liftCoords, Term.shiftBy_eval, envCons]

theorem relationEnv_evalTerms (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V)
    (τ : Fin n → Fin tags) (κ : Fin n → Fin dim → Term V m) (σ : Env A.card m)
    {arity : Nat} (ts : Fin arity → Term W n) :
    relationEnv (fun j => (ts j).eval (I.apply A) (coordEnv A τ κ σ)) =
      fun k => (I.termCoords κ (ts (finProdFinEquiv.symm k).1)
        (finProdFinEquiv.symm k).2).eval A σ := by
  funext k
  exact congrArg (fun p => p.2 (finProdFinEquiv.symm k).2)
    (I.termCoords_eval A τ κ σ (ts (finProdFinEquiv.symm k).1))

theorem pullbackWith_sat (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V)
    (φ : Formula W n) (τ : Fin n → Fin tags) (κ : Fin n → Fin dim → Term V m)
    (σ : Env A.card m) :
    (I.pullbackWith φ τ κ).Sat A σ ↔ φ.Sat (I.apply A) (coordEnv A τ κ σ) := by
  induction φ generalizing m with
  | relApp i ts =>
    rw [pullbackWith, Formula.subst_sat]
    change _ ↔ (I.relFormula i (fun j =>
      (elementEquiv A.card tags dim ((ts j).eval (I.apply A) (coordEnv A τ κ σ))).1)).Sat A
      (relationEnv (fun j => (ts j).eval (I.apply A) (coordEnv A τ κ σ)))
    simp only [relationEnv_evalTerms, termCoords_eval]
  | eq t₁ t₂ =>
    simp only [pullbackWith, Formula.Sat]
    rw [← (elementEquiv A.card tags dim).injective.eq_iff, termCoords_eval, termCoords_eval]
    split <;> simp_all [Formula.conjFin_sat, Formula.Sat, Formula.falsum_sat, funext_iff]
  | neg φ ih => exact not_congr (ih τ κ σ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ τ κ σ) (ihψ τ κ σ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ τ κ σ) (ihψ τ κ σ)
  | exist φ ih =>
    simp only [pullbackWith, Formula.disjFin_sat, Formula.existBlock_sat, ih, coordEnv_lift,
      Formula.Sat]
    constructor
    · rintro ⟨tag, v, h⟩; exact ⟨(elementEquiv A.card tags dim).symm (tag, v), h⟩
    · rintro ⟨x, h⟩
      exact ⟨(elementEquiv A.card tags dim x).1, (elementEquiv A.card tags dim x).2,
        by simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h⟩
  | all φ ih =>
    simp only [pullbackWith, Formula.conjFin_sat, Formula.allBlock_sat, ih, coordEnv_lift,
      Formula.Sat]
    constructor
    · intro h x
      simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using
        h (elementEquiv A.card tags dim x).1 (elementEquiv A.card tags dim x).2
    · intro h tag v; exact h ((elementEquiv A.card tags dim).symm (tag, v))

end Complexity.DescriptiveComplexity.TaggedFOInterpretation
