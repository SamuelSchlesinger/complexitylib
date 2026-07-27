/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.SecondOrder.Semantics
public import Complexitylib.DescriptiveComplexity.FirstOrder.Isomorphism

/-!
# Second-order logic: isomorphism invariance

Second-order satisfaction is preserved by isomorphisms, so second-order (and hence
`∃SO`) sentences define order-independent queries. This is the second-order analogue
of `Formula.sat_iso` / `Sentence.orderIndependent`, and it is step 3 of the Fagin
decomposition (roadmap L6).

The extra ingredient over the first-order case is transporting a **relation**
environment across the isomorphism (`REnv.map`), together with the fact that this
transport commutes with extending the environment by a fresh relation
(`rCons_map`). Second-order quantifiers then match up by pushing/pulling the
witnessing relations through the isomorphism.

## Main definitions and results

- `DescriptiveComplexity.REnv.map`, `rCons_map` — transport of relation
  environments across an isomorphism, and its compatibility with `rCons`.
- `SOFormula.sat_iso`, `SOSentence.models_iso` — second-order satisfaction is
  isomorphism-invariant.
- `SODefinable`, `SODefinable.orderIndependent` — second-order definable queries
  are order-independent.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary} {A B : FinStruct V}

/-- Transport a relation environment across an isomorphism: a relation on `A` is
    reinterpreted on `B` by pulling arguments back through `f⁻¹`. -/
def REnv.map (f : Iso A B) {rctx : List Nat} (ρ : REnv A.card rctx) : REnv B.card rctx :=
  fun r args => ρ r (f.invFun ∘ args)

/-- Transport commutes with extending the environment by a fresh relation. -/
theorem rCons_map (f : Iso A B) {k : Nat} {rctx : List Nat}
    (S : (Fin k → Fin A.card) → Prop) (ρ : REnv A.card rctx) :
    REnv.map f (rCons S ρ) = rCons (fun args => S (f.invFun ∘ args)) (REnv.map f ρ) := by
  funext r args
  rcases r with ⟨(_ | i), h⟩ <;> rfl

/-- Round-trip helper: pushing a relation through `f⁻¹` then `f` recovers it. -/
private theorem push_pull (f : Iso A B) {k : Nat} (S : (Fin k → Fin B.card) → Prop) :
    (fun args => (fun args => S (f.toFun ∘ args)) (f.invFun ∘ args)) = S := by
  funext args
  show S (f.toFun ∘ f.invFun ∘ args) = S args
  rw [show (f.toFun ∘ f.invFun ∘ args : Fin k → Fin B.card) = args from by
    funext j; exact f.right_inv (args j)]

/-- **Second-order satisfaction is isomorphism-invariant.** Along an isomorphism
    `f : A ≅ B`, a formula holds at `(σ, ρ)` iff it holds at the transported
    environments `(f ∘ σ, f₊ρ)`. -/
theorem SOFormula.sat_iso (f : Iso A B) :
    ∀ {rctx : List Nat} {n : Nat} (φ : SOFormula V rctx n)
      (σ : Env A.card n) (ρ : REnv A.card rctx),
      φ.Sat A σ ρ ↔ φ.Sat B (f.toFun ∘ σ) (REnv.map f ρ) := by
  intro rctx n φ
  induction φ with
  | relApp i args =>
    intro σ ρ; simp only [SOFormula.Sat]
    have : (fun j => (args j).eval B (f.toFun ∘ σ)) = (f.toFun ∘ fun j => (args j).eval A σ) := by
      funext j; exact Term.eval_iso f σ (args j)
    rw [this]; exact f.rel_map i _
  | soRelApp r args =>
    intro σ ρ; simp only [SOFormula.Sat, REnv.map]
    have : (f.invFun ∘ fun j => (args j).eval B (f.toFun ∘ σ)) = (fun j => (args j).eval A σ) := by
      funext j; simp only [Function.comp]; rw [Term.eval_iso f σ (args j), f.left_inv]
    rw [this]
  | eq t₁ t₂ =>
    intro σ ρ; simp only [SOFormula.Sat]
    rw [Term.eval_iso f σ t₁, Term.eval_iso f σ t₂]
    exact ⟨fun h => by rw [h], fun h => f.toFun_injective h⟩
  | neg φ ih => intro σ ρ; exact not_congr (ih σ ρ)
  | conj φ ψ ihφ ihψ => intro σ ρ; exact and_congr (ihφ σ ρ) (ihψ σ ρ)
  | disj φ ψ ihφ ihψ => intro σ ρ; exact or_congr (ihφ σ ρ) (ihψ σ ρ)
  | exist φ ih =>
    intro σ ρ; simp only [SOFormula.Sat]
    constructor
    · rintro ⟨a, ha⟩; exact ⟨f.toFun a, by rw [← envCons_comp]; exact (ih (envCons a σ) ρ).mp ha⟩
    · rintro ⟨b, hb⟩
      exact ⟨f.invFun b, by rw [ih (envCons (f.invFun b) σ) ρ, envCons_comp, f.right_inv]; exact hb⟩
  | all φ ih =>
    intro σ ρ; simp only [SOFormula.Sat]
    constructor
    · intro ha b; have := ha (f.invFun b)
      rw [ih (envCons (f.invFun b) σ) ρ, envCons_comp, f.right_inv] at this; exact this
    · intro hb a; rw [ih (envCons a σ) ρ, envCons_comp]; exact hb (f.toFun a)
  | soExist k φ ih =>
    intro σ ρ; simp only [SOFormula.Sat]
    constructor
    · rintro ⟨S, hS⟩
      exact ⟨fun args => S (f.invFun ∘ args), by rw [← rCons_map]; exact (ih σ (rCons S ρ)).mp hS⟩
    · rintro ⟨S, hS⟩
      exact ⟨fun args => S (f.toFun ∘ args), by
        rw [ih σ (rCons (fun args => S (f.toFun ∘ args)) ρ), rCons_map, push_pull f S]; exact hS⟩
  | soAll k φ ih =>
    intro σ ρ; simp only [SOFormula.Sat]
    constructor
    · intro ha S; have := ha (fun args => S (f.toFun ∘ args))
      rw [ih σ (rCons (fun args => S (f.toFun ∘ args)) ρ), rCons_map, push_pull f S] at this
      exact this
    · intro hb S; rw [ih σ (rCons S ρ), rCons_map]; exact hb _

/-- **Second-order sentences are isomorphism-invariant.** -/
theorem SOSentence.models_iso (f : Iso A B) (φ : SOSentence V) :
    SOSentence.Models A φ ↔ SOSentence.Models B φ := by
  unfold SOSentence.Models
  rw [SOFormula.sat_iso f φ (emptyEnv A.card) (emptyREnv A.card)]
  have he : (f.toFun ∘ emptyEnv A.card) = emptyEnv B.card := emptyEnv_comp f.toFun
  have hr : REnv.map f (emptyREnv A.card) = emptyREnv B.card := by
    funext r; exact absurd r.isLt (by simp)
  rw [he, hr]

/-- A Boolean query is **second-order definable** if some SO sentence defines it. -/
def SODefinable (Q : BooleanQuery V) : Prop :=
  ∃ φ : SOSentence V, ∀ A : FinStruct V, Q A ↔ SOSentence.Models A φ

/-- **Second-order definable queries are order-independent** — in particular every
    `∃SO` query is legitimate, as Fagin's theorem requires. -/
theorem SODefinable.orderIndependent {Q : BooleanQuery V} (hQ : SODefinable Q) :
    Q.IsOrderIndependent := by
  obtain ⟨φ, hφ⟩ := hQ
  intro A B ⟨f⟩
  rw [hφ A, hφ B]
  exact SOSentence.models_iso f φ

/-- Second-order definable queries are closed under complement (via `¬`). -/
theorem SODefinable.complement {Q : BooleanQuery V} (hQ : SODefinable Q) :
    SODefinable Q.complement := by
  obtain ⟨φ, hφ⟩ := hQ
  exact ⟨SOFormula.neg φ, fun A => by
    simp only [BooleanQuery.complement, hφ A, SOSentence.Models, SOFormula.Sat]⟩

/-- Second-order definable queries are closed under intersection (via `∧`). -/
theorem SODefinable.inter {Q₁ Q₂ : BooleanQuery V}
    (h₁ : SODefinable Q₁) (h₂ : SODefinable Q₂) : SODefinable (Q₁.inter Q₂) := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨SOFormula.conj φ ψ, fun A => by
    simp only [BooleanQuery.inter, hφ A, hψ A, SOSentence.Models, SOFormula.Sat]⟩

/-- Second-order definable queries are closed under union (via `∨`). -/
theorem SODefinable.union {Q₁ Q₂ : BooleanQuery V}
    (h₁ : SODefinable Q₁) (h₂ : SODefinable Q₂) : SODefinable (Q₁.union Q₂) := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨SOFormula.disj φ ψ, fun A => by
    simp only [BooleanQuery.union, hφ A, hψ A, SOSentence.Models, SOFormula.Sat]⟩

end DescriptiveComplexity

end Complexity
