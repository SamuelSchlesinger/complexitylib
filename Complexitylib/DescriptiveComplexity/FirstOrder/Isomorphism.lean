/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.Query
public import Complexitylib.DescriptiveComplexity.FirstOrder.Semantics

/-!
  Isomorphism preservation for first-order logic.

  Key results:
  1. Term evaluation commutes with isomorphisms
  2. Satisfaction is preserved by isomorphisms
  3. FO sentences are order-independent (Immerman Proposition 1.16)
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary} {A B : FinStruct V}

/-- Term evaluation commutes with isomorphisms. -/
theorem Term.eval_iso (f : Iso A B) (σ : Env A.card n) (t : Term V n) :
    t.eval B (f.toFun ∘ σ) = f.toFun (t.eval A σ) := by
  cases t with
  | var i => rfl
  | const j => exact (f.const_map j).symm

/-- Satisfaction is preserved by isomorphisms. -/
theorem Formula.sat_iso (f : Iso A B) (σ : Env A.card n) (φ : Formula V n) :
    φ.Sat A σ ↔ φ.Sat B (f.toFun ∘ σ) := by
  induction φ with
  | relApp i args =>
    simp only [Formula.Sat]
    have : (fun j => (args j).eval B (f.toFun ∘ σ)) = (f.toFun ∘ fun j => (args j).eval A σ) := by
      funext j
      exact Term.eval_iso f σ (args j)
    rw [this]
    exact f.rel_map i _
  | eq t₁ t₂ =>
    simp only [Formula.Sat]
    constructor
    · intro h
      rw [Term.eval_iso f σ t₁, Term.eval_iso f σ t₂, h]
    · intro h
      rw [Term.eval_iso f σ t₁, Term.eval_iso f σ t₂] at h
      exact f.toFun_injective h
  | neg φ ih =>
    simp only [Formula.Sat]
    exact not_congr (ih σ)
  | conj φ ψ ihφ ihψ =>
    simp only [Formula.Sat]
    exact and_congr (ihφ σ) (ihψ σ)
  | disj φ ψ ihφ ihψ =>
    simp only [Formula.Sat]
    exact or_congr (ihφ σ) (ihψ σ)
  | exist φ ih =>
    simp only [Formula.Sat]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨f.toFun a, by rw [← envCons_comp]; exact (ih (envCons a σ)).mp ha⟩
    · rintro ⟨b, hb⟩
      exact ⟨f.invFun b, by
        rw [ih (envCons (f.invFun b) σ), envCons_comp, f.right_inv]
        exact hb⟩
  | all φ ih =>
    simp only [Formula.Sat]
    constructor
    · intro ha b
      have := ha (f.invFun b)
      rw [ih (envCons (f.invFun b) σ), envCons_comp, f.right_inv] at this
      exact this
    · intro hb a
      rw [ih (envCons a σ), envCons_comp]
      exact hb (f.toFun a)

/-- FO sentences are order-independent (Immerman Proposition 1.16). -/
theorem Sentence.orderIndependent (φ : Sentence V) :
    BooleanQuery.IsOrderIndependent (fun A => A ⊨ φ) := by
  intro A B ⟨f⟩
  simp only [Sentence.Models]
  rw [Formula.sat_iso f (emptyEnv A.card), emptyEnv_comp]

end DescriptiveComplexity

end Complexity
