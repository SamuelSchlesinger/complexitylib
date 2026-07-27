/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.SecondOrder.Syntax
public import Complexitylib.DescriptiveComplexity.FirstOrder.Semantics

/-!
# Second-order logic: semantics

Satisfaction of a second-order formula needs, besides the first-order element
environment `Env`, a **relation environment** `REnv` interpreting each relation
variable in the de Bruijn context `rctx` as a relation of its arity on the
universe. Second-order quantifiers range over all such relations, extending the
relation environment with `rCons`.

This is step 2 of the Fagin decomposition (roadmap L6). The FO fragment embeds
faithfully: `SOFormula.ofFormula_sat` shows the embedding preserves satisfaction,
so first-order truth is a special case of second-order truth
(`SOSentence.models_ofFormula`).

## Main definitions and results

- `DescriptiveComplexity.REnv`, `rCons`, `emptyREnv` — relation environments.
- `DescriptiveComplexity.SOFormula.Sat`, `SOSentence.Models` — SO satisfaction.
- `SOFormula.ofFormula_sat`, `SOSentence.models_ofFormula` — the FO embedding is
  truth-preserving.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- A relation-variable assignment: interprets each relation variable in `rctx`
    as a relation of its arity on the universe `Fin card`. -/
def REnv (card : Nat) (rctx : List Nat) : Type :=
  (r : Fin rctx.length) → (Fin (rctx.get r) → Fin card) → Prop

/-- Extend a relation environment with a fresh arity-`k` relation at index 0. -/
def rCons {card k : Nat} {rctx : List Nat}
    (S : (Fin k → Fin card) → Prop) (ρ : REnv card rctx) : REnv card (k :: rctx) :=
  fun r => match r with
    | ⟨0, _⟩ => S
    | ⟨i + 1, h⟩ => ρ ⟨i, by simpa using h⟩

/-- The empty relation environment (no relation variables). -/
def emptyREnv (card : Nat) : REnv card [] := fun r => absurd r.isLt (by simp)

variable {V : Vocabulary}

/-- Satisfaction of a second-order formula in a structure under element and
    relation environments. Second-order quantifiers range over all relations of
    the quantified arity. -/
def SOFormula.Sat (A : FinStruct V) : {rctx : List Nat} → {n : Nat} →
    Env A.card n → REnv A.card rctx → SOFormula V rctx n → Prop
  | _, _, σ, _, .relApp i args => A.rel i (fun j => (args j).eval A σ)
  | _, _, σ, ρ, .soRelApp r args => ρ r (fun j => (args j).eval A σ)
  | _, _, σ, _, .eq t₁ t₂ => t₁.eval A σ = t₂.eval A σ
  | _, _, σ, ρ, .neg φ => ¬ SOFormula.Sat A σ ρ φ
  | _, _, σ, ρ, .conj φ ψ => SOFormula.Sat A σ ρ φ ∧ SOFormula.Sat A σ ρ ψ
  | _, _, σ, ρ, .disj φ ψ => SOFormula.Sat A σ ρ φ ∨ SOFormula.Sat A σ ρ ψ
  | _, _, σ, ρ, .exist φ => ∃ a : Fin A.card, SOFormula.Sat A (envCons a σ) ρ φ
  | _, _, σ, ρ, .all φ => ∀ a : Fin A.card, SOFormula.Sat A (envCons a σ) ρ φ
  | _, _, σ, ρ, .soExist k φ => ∃ S : (Fin k → Fin A.card) → Prop, SOFormula.Sat A σ (rCons S ρ) φ
  | _, _, σ, ρ, .soAll k φ => ∀ S : (Fin k → Fin A.card) → Prop, SOFormula.Sat A σ (rCons S ρ) φ

/-- A structure models a second-order sentence under the empty environments. -/
def SOSentence.Models (A : FinStruct V) (φ : SOSentence V) : Prop :=
  φ.Sat A (emptyEnv A.card) (emptyREnv A.card)

/-- **The first-order embedding preserves satisfaction.** An FO formula embedded
    into second-order logic is satisfied under `(σ, ρ)` exactly when the original
    is satisfied under `σ` — the relation environment `ρ` is irrelevant, since the
    embedded formula never mentions relation variables. -/
theorem SOFormula.ofFormula_sat (A : FinStruct V) {rctx : List Nat} (ρ : REnv A.card rctx) :
    ∀ {n : Nat} (φ : Formula V n) (σ : Env A.card n),
      (SOFormula.ofFormula φ rctx).Sat A σ ρ ↔ φ.Sat A σ := by
  intro n φ
  induction φ with
  | relApp i args => intro σ; exact Iff.rfl
  | eq a b => intro σ; exact Iff.rfl
  | neg φ ih => intro σ; exact not_congr (ih σ)
  | conj φ ψ ihφ ihψ => intro σ; exact and_congr (ihφ σ) (ihψ σ)
  | disj φ ψ ihφ ihψ => intro σ; exact or_congr (ihφ σ) (ihψ σ)
  | exist φ ih => intro σ; exact exists_congr (fun a => ih (envCons a σ))
  | all φ ih => intro σ; exact forall_congr' (fun a => ih (envCons a σ))

/-- **First-order truth is a special case of second-order truth.** A structure
    models an FO sentence iff it models its second-order embedding. -/
theorem SOSentence.models_ofFormula (A : FinStruct V) (φ : Sentence V) :
    SOSentence.Models A (SOFormula.ofFormula φ []) ↔ Sentence.Models A φ :=
  SOFormula.ofFormula_sat A (emptyREnv A.card) φ (emptyEnv A.card)

end DescriptiveComplexity

end Complexity
