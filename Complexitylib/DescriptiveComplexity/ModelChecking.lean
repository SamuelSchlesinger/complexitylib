/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.FirstOrder.Semantics
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual

/-!
# Computable first-order model checking

Over a *finite* structure the quantifiers of first-order logic range over a finite
universe, so satisfaction is decidable. This module gives a `Bool`-valued evaluator
`Formula.evalB` over a decidable structure (`DecFinStruct`) and proves it agrees
with the propositional `Sat`/`Models`.

Computable FO model checking is a prerequisite for several roadmap L6 milestones:
the `∃SO ⊆ NP` direction of Fagin's theorem (an `NP` machine guesses the witnessing
relations and *checks the FO matrix* in polynomial time), the Immerman–Vardi
characterization, and the `FO ⊆ AC⁰` bridge.

## Main definitions and results

- `DescriptiveComplexity.Formula.evalB`, `Formula.evalB_eq_sat` — the evaluator and
  its correctness.
- `DescriptiveComplexity.Sentence.evalB`, `Sentence.evalB_eq_models` — the sentence
  form.
-/


public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- Computable `Bool`-valued first-order model checking over a *decidable* finite
    structure: quantifiers range over the finite universe `Fin card` via
    `List.finRange`. -/
def Formula.evalB (A : DecFinStruct V) : {n : Nat} → Env A.card n → Formula V n → Bool
  | _, σ, .relApp i args => A.rel i (fun j => (args j).eval A.toFinStruct σ)
  | _, σ, .eq t₁ t₂ => decide ((t₁.eval A.toFinStruct σ) = (t₂.eval A.toFinStruct σ))
  | _, σ, .neg φ => !(Formula.evalB A σ φ)
  | _, σ, .conj φ ψ => Formula.evalB A σ φ && Formula.evalB A σ ψ
  | _, σ, .disj φ ψ => Formula.evalB A σ φ || Formula.evalB A σ ψ
  | _, σ, .exist φ => (List.finRange A.card).any (fun a => Formula.evalB A (envCons a σ) φ)
  | _, σ, .all φ => (List.finRange A.card).all (fun a => Formula.evalB A (envCons a σ) φ)

/-- **FO model checking is correct**: the `Bool` evaluator agrees with
    satisfaction. -/
theorem Formula.evalB_eq_sat (A : DecFinStruct V) :
    ∀ {n : Nat} (φ : Formula V n) (σ : Env A.card n),
      (Formula.evalB A σ φ = true) ↔ φ.Sat A.toFinStruct σ := by
  intro n φ
  induction φ with
  | relApp i args => intro σ; exact Iff.rfl
  | eq t₁ t₂ => intro σ; simp only [Formula.evalB, Formula.Sat, decide_eq_true_eq]
  | neg φ ih =>
    intro σ
    simp only [Formula.evalB, Formula.Sat, Bool.not_eq_true', ← ih σ, Bool.not_eq_true]
  | conj φ ψ ihφ ihψ => intro σ; simp only [Formula.evalB, Formula.Sat, Bool.and_eq_true, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => intro σ; simp only [Formula.evalB, Formula.Sat, Bool.or_eq_true, ihφ, ihψ]
  | exist φ ih =>
    intro σ
    simp only [Formula.evalB, Formula.Sat, List.any_eq_true]
    constructor
    · rintro ⟨a, _, ha⟩; exact ⟨a, (ih _).mp ha⟩
    · rintro ⟨a, ha⟩; exact ⟨a, List.mem_finRange a, (ih _).mpr ha⟩
  | all φ ih =>
    intro σ
    simp only [Formula.evalB, Formula.Sat, List.all_eq_true]
    constructor
    · intro h a; exact (ih _).mp (h a (List.mem_finRange a))
    · intro h a _; exact (ih _).mpr (h a)

/-- Model checking of a first-order *sentence* on a decidable structure. -/
def Sentence.evalB (A : DecFinStruct V) (φ : Sentence V) : Bool :=
  Formula.evalB A (emptyEnv A.card) φ

/-- Sentence model checking is correct. -/
theorem Sentence.evalB_eq_models (A : DecFinStruct V) (φ : Sentence V) :
    (Sentence.evalB A φ = true) ↔ Sentence.Models A.toFinStruct φ :=
  Formula.evalB_eq_sat A φ (emptyEnv A.card)

/-- **First-order truth over a finite structure is decidable** (via the correct
    `Bool` evaluator). -/
instance decidableModels (A : DecFinStruct V) (φ : Sentence V) :
    Decidable (Sentence.Models A.toFinStruct φ) :=
  decidable_of_iff _ (Sentence.evalB_eq_models A φ)

end DescriptiveComplexity

end Complexity
