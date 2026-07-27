/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Vocabulary

/-!
  First-order logic syntax: terms, formulas, sentences, derived connectives.

  Follows Immerman Definition 1.11.
  Terms are variables (de Bruijn indexed) or vocabulary constants.
  Formulas are indexed by the number of free variables.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- Terms of first-order logic over vocabulary `V` with `n` free variables. -/
inductive Term (V : Vocabulary) (n : Nat) where
  | var : Fin n → Term V n
  | const : Fin V.numConsts → Term V n

/-- Formulas of first-order logic over vocabulary `V` with `n` free variables. -/
inductive Formula (V : Vocabulary) : Nat → Type where
  | relApp : (i : Fin V.numRels) → (Fin (V.relArity i) → Term V n) → Formula V n
  | eq : Term V n → Term V n → Formula V n
  | neg : Formula V n → Formula V n
  | conj : Formula V n → Formula V n → Formula V n
  | disj : Formula V n → Formula V n → Formula V n
  | exist : Formula V (n + 1) → Formula V n
  | all : Formula V (n + 1) → Formula V n

/-- A sentence is a formula with no free variables. -/
abbrev Sentence (V : Vocabulary) := Formula V 0

namespace Formula

/-- Material implication. -/
def impl (φ ψ : Formula V n) : Formula V n := disj (neg φ) ψ

/-- Biconditional (if and only if). -/
def biconditional (φ ψ : Formula V n) : Formula V n := conj (impl φ ψ) (impl ψ φ)

/-- Verum (always true): ∀x₀. x₀ = x₀. Works at any `n` including 0. -/
def verum : Formula V n := all (eq (.var ⟨0, by omega⟩) (.var ⟨0, by omega⟩))

/-- Falsum (always false): ¬⊤. -/
def falsum : Formula V n := neg verum

/-- Quantifier rank of a formula. -/
def quantifierRank : Formula V n → Nat
  | .relApp _ _ => 0
  | .eq _ _ => 0
  | .neg φ => φ.quantifierRank
  | .conj φ ψ => max φ.quantifierRank ψ.quantifierRank
  | .disj φ ψ => max φ.quantifierRank ψ.quantifierRank
  | .exist φ => φ.quantifierRank + 1
  | .all φ => φ.quantifierRank + 1

/-- Size (number of nodes) of a formula. -/
def size : Formula V n → Nat
  | .relApp _ _ => 1
  | .eq _ _ => 1
  | .neg φ => φ.size + 1
  | .conj φ ψ => φ.size + ψ.size + 1
  | .disj φ ψ => φ.size + ψ.size + 1
  | .exist φ => φ.size + 1
  | .all φ => φ.size + 1

end Formula

end DescriptiveComplexity

end Complexity
