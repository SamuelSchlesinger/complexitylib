/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.ModelChecking.Defs

/-!
# Correctness of Boolean relation tables and matrix evaluation

Boolean relation tables faithfully and exhaustively present propositional
relation environments. Structural induction on an FO matrix proves its Boolean
evaluator agrees with satisfaction under the represented environment.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem toREnv_cons_internal {card k : Nat} {rctx : List Nat}
    (S : (Fin k → Fin card) → Bool) (ρ : DecREnv card rctx) :
    (ρ.cons S).toREnv = rCons (fun args => S args = true) ρ.toREnv := by
  funext r args
  cases r using Fin.cases <;> rfl

theorem toREnv_injective_internal (card : Nat) (rctx : List Nat) :
    Function.Injective (DecREnv.toREnv (card := card) (rctx := rctx)) := by
  intro ρ τ h
  funext r args
  apply Bool.eq_iff_iff.mpr
  exact Iff.of_eq (congrArg (fun env => env r args) h)

theorem toREnv_surjective_internal (card : Nat) (rctx : List Nat) :
    Function.Surjective (DecREnv.toREnv (card := card) (rctx := rctx)) := by
  classical
  intro ρ
  refine ⟨fun r args => decide (ρ r args), ?_⟩
  funext r args
  simp [DecREnv.toREnv]

theorem evalMatrixB_eq_sat_internal {V : Vocabulary} (A : DecFinStruct V)
    {rctx : List Nat} {n : Nat} (φ : SOFormula V rctx n) :
    ∀ (h : φ.IsFOMatrix) (σ : Env A.card n) (ρ : DecREnv A.card rctx),
      φ.evalMatrixB A h σ ρ = true ↔ φ.Sat A.toFinStruct σ ρ.toREnv := by
  induction φ with
  | relApp i args => intro h σ ρ; rfl
  | soRelApp r args => intro h σ ρ; rfl
  | eq a b =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixB, SOFormula.Sat, decide_eq_true_eq]
  | neg φ ih =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixB, SOFormula.Sat, Bool.not_eq_true',
      ← ih h σ ρ, Bool.not_eq_true]
  | conj φ ψ ihφ ihψ =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixB, SOFormula.Sat, Bool.and_eq_true, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixB, SOFormula.Sat, Bool.or_eq_true, ihφ, ihψ]
  | exist φ ih =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixB, SOFormula.Sat, List.any_eq_true,
      List.mem_finRange, true_and]
    exact exists_congr fun a => ih h (envCons a σ) ρ
  | all φ ih =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixB, SOFormula.Sat, List.all_eq_true,
      List.mem_finRange, forall_const]
    exact forall_congr' fun a => ih h (envCons a σ) ρ
  | soExist k φ ih => intro h; exact h.elim
  | soAll k φ ih => intro h; exact h.elim

end Complexity.DescriptiveComplexity
