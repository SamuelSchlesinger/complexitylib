/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.FirstOrder.Semantics

/-!
# First-order substitution

Simultaneous substitution of terms for the free (de Bruijn) variables of a formula,
and its semantic correctness — the **substitution theorem**
`Formula.subst_sat`: satisfaction of `φ.subst ρ` under `σ` equals satisfaction of `φ`
under the environment `k ↦ ⟦ρ k⟧_σ`.

The de Bruijn bookkeeping is handled by `Term.shift` (raise every index by one, for
crossing a binder) and `liftSubst` (extend a substitution under a binder: the new
variable 0 stays, everything else is shifted). This is the engine behind the
fundamental theorem of first-order interpretations (roadmap L6): the transport of a
formula along an `FOInterpretation`.

## Main definitions and results

- `Term.shift`, `Term.shift_eval` — index shift and its evaluation invariance.
- `Term.substTerm`, `Term.substTerm_eval` — term substitution and its evaluation.
- `liftSubst`, `liftSubst_eval` — lifting a substitution under a binder.
- `Formula.subst`, `Formula.quantifierRank_subst` — formula substitution preserves
  quantifier rank.
- `Formula.subst_sat` — the substitution theorem.
-/


public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- Shift every variable of a term up by one de Bruijn index (to cross a binder). -/
def Term.shift {n : Nat} : Term V n → Term V (n + 1)
  | .var i => Term.var ⟨i.val + 1, by omega⟩
  | .const c => Term.const c

/-- Shifting a term and evaluating under an extended environment recovers the original
    evaluation: the fresh variable `0` is never referenced by a shifted term. -/
theorem Term.shift_eval {n : Nat} (A : FinStruct V) (a : Fin A.card) (σ : Env A.card n)
    (t : Term V n) : Term.eval A (envCons a σ) t.shift = Term.eval A σ t := by
  cases t with
  | var i => show (envCons a σ) _ = σ i; rw [envCons_succ]
  | const c => rfl

/-- Apply a substitution (a term for each variable) to a term. -/
def Term.substTerm {m n : Nat} (ρ : Fin m → Term V n) : Term V m → Term V n
  | .var j => ρ j
  | .const c => Term.const c

/-- Evaluating a substituted term is evaluating the original under the substituted
    environment. -/
theorem Term.substTerm_eval {m n : Nat} (A : FinStruct V) (σ : Env A.card n)
    (ρ : Fin m → Term V n) (t : Term V m) :
    Term.eval A σ (t.substTerm ρ) = Term.eval A (fun k => Term.eval A σ (ρ k)) t := by
  cases t with
  | var j => rfl
  | const c => rfl

/-- Lift a substitution under a binder: variable `0` maps to itself, and every other
    variable takes its old (shifted) image. -/
def liftSubst {m n : Nat} (ρ : Fin m → Term V n) : Fin (m + 1) → Term V (n + 1) :=
  fun i => if h : i.val = 0 then Term.var ⟨0, by omega⟩ else (ρ ⟨i.val - 1, by omega⟩).shift

/-- The environment induced by a lifted substitution is the extension (by the new
    element) of the environment induced by the original — the compatibility fact that
    drives the quantifier case of the substitution theorem. -/
theorem liftSubst_eval {m n : Nat} (A : FinStruct V) (a : Fin A.card) (σ : Env A.card n)
    (ρ : Fin m → Term V n) :
    (fun k => Term.eval A (envCons a σ) (liftSubst ρ k))
      = envCons a (fun k => Term.eval A σ (ρ k)) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [liftSubst, Term.eval, envCons]
  | succ j =>
    have hne : (Fin.succ j).val ≠ 0 := by simp [Fin.val_succ]
    simp only [liftSubst, dite_eq_right hne, Term.shift_eval]
    simp [envCons, Fin.val_succ]

/-- Simultaneous substitution of terms for the free variables of a formula. Under a
    quantifier the substitution is lifted, so de Bruijn indices stay aligned. -/
def Formula.subst : {m n : Nat} → Formula V m → (Fin m → Term V n) → Formula V n
  | _, _, .relApp i ts, ρ => .relApp i (fun k => (ts k).substTerm ρ)
  | _, _, .eq t₁ t₂, ρ => .eq (t₁.substTerm ρ) (t₂.substTerm ρ)
  | _, _, .neg φ, ρ => .neg (φ.subst ρ)
  | _, _, .conj φ ψ, ρ => .conj (φ.subst ρ) (ψ.subst ρ)
  | _, _, .disj φ ψ, ρ => .disj (φ.subst ρ) (ψ.subst ρ)
  | _, _, .exist φ, ρ => .exist (φ.subst (liftSubst ρ))
  | _, _, .all φ, ρ => .all (φ.subst (liftSubst ρ))

/-- Substituting terms for free variables preserves quantifier rank exactly. -/
theorem Formula.quantifierRank_subst {m n : Nat} (φ : Formula V m)
    (ρ : Fin m → Term V n) :
    (φ.subst ρ).quantifierRank = φ.quantifierRank := by
  induction φ generalizing n <;>
    simp [Formula.subst, Formula.quantifierRank, *]

/-- **The substitution theorem.** Satisfaction of a substituted formula under `σ`
    equals satisfaction of the original formula under the environment that evaluates
    each substituted term. -/
theorem Formula.subst_sat (A : FinStruct V) :
    ∀ {m n : Nat} (σ : Env A.card n) (ρ : Fin m → Term V n) (φ : Formula V m),
      Formula.Sat A σ (φ.subst ρ) ↔ Formula.Sat A (fun k => Term.eval A σ (ρ k)) φ := by
  intro m n σ ρ φ
  induction φ generalizing n with
  | relApp i ts => simp [Formula.subst, Formula.Sat, Term.substTerm_eval]
  | eq t₁ t₂ => simp [Formula.subst, Formula.Sat, Term.substTerm_eval]
  | neg φ ih => simp [Formula.subst, Formula.Sat, ih]
  | conj φ ψ ihφ ihψ => simp [Formula.subst, Formula.Sat, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [Formula.subst, Formula.Sat, ihφ, ihψ]
  | exist φ ih =>
    simp only [Formula.subst, Formula.Sat]
    apply exists_congr; intro a
    rw [ih (envCons a σ) (liftSubst ρ), liftSubst_eval]
  | all φ ih =>
    simp only [Formula.subst, Formula.Sat]
    apply forall_congr'; intro a
    rw [ih (envCons a σ) (liftSubst ρ), liftSubst_eval]

end DescriptiveComplexity

end Complexity
