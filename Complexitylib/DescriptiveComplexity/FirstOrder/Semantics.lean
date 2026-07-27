/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Structure
public import Complexitylib.DescriptiveComplexity.Env
public import Complexitylib.DescriptiveComplexity.FirstOrder.Syntax

/-!
  First-order logic semantics: term evaluation, formula satisfaction, models.

  Follows Immerman Definition 1.11 (semantics part).
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- Evaluate a term in a structure under an environment. -/
def Term.eval (A : FinStruct V) (σ : Env A.card n) : Term V n → Fin A.card
  | .var i => σ i
  | .const j => A.const j

/-- Satisfaction of a formula in a structure under an environment. -/
def Formula.Sat (A : FinStruct V) (σ : Env A.card n) : Formula V n → Prop
  | .relApp i args => A.rel i (fun j => (args j).eval A σ)
  | .eq t₁ t₂ => t₁.eval A σ = t₂.eval A σ
  | .neg φ => ¬ Sat A σ φ
  | .conj φ ψ => Sat A σ φ ∧ Sat A σ ψ
  | .disj φ ψ => Sat A σ φ ∨ Sat A σ ψ
  | .exist φ => ∃ a : Fin A.card, Sat A (envCons a σ) φ
  | .all φ => ∀ a : Fin A.card, Sat A (envCons a σ) φ

/-- A structure models a sentence if it is satisfied under the empty environment. -/
def Sentence.Models (A : FinStruct V) (φ : Sentence V) : Prop :=
  φ.Sat A (emptyEnv A.card)

/-- Notation: `A ⊨ φ` for `Sentence.Models A φ`. -/
scoped notation:50 A " ⊨ " φ => Sentence.Models A φ

theorem Formula.verum_sat (A : FinStruct V) (σ : Env A.card n) :
    Formula.verum.Sat A σ ↔ True := by
  simp [Formula.verum, Formula.Sat]

theorem Formula.falsum_sat (A : FinStruct V) (σ : Env A.card n) :
    Formula.falsum.Sat A σ ↔ False := by
  simp [Formula.falsum, Formula.Sat, Formula.verum_sat]

end DescriptiveComplexity

end Complexity
