/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Translation
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The observational category of circuit translations

Dependent gate indices make raw compiler output too intensional for useful
categorical equality. We quotient translations by the behavior they induce on
all interpretations over a fixed carrier and on all weighted cost models.
Compilation respects this relation, and the quotient forms an ordinary
Mathlib category.
-/

@[expose] public section

namespace Algebraic

namespace Translation

/-- Two translations are observationally equivalent over `U` when they induce
the same interpretation pullback on `U` and the same pullback of every cost
model. -/
structure EquivalentOn
    (U : Type u)
    (left right : Translation σ τ) : Prop where
  pull_eq : ∀ interpretation : Interpretation τ U,
    left.pull interpretation = right.pull interpretation
  pullCost_eq : ∀ operationCost : OperationCost τ,
    left.pullCost operationCost = right.pullCost operationCost

namespace EquivalentOn

theorem refl (translation : Translation σ τ) :
    EquivalentOn U translation translation :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem symm
    {left right : Translation σ τ}
    (equivalent : EquivalentOn U left right) :
    EquivalentOn U right left :=
  ⟨fun interpretation => (equivalent.pull_eq interpretation).symm,
    fun operationCost => (equivalent.pullCost_eq operationCost).symm⟩

theorem trans
    {first second third : Translation σ τ}
    (left : EquivalentOn U first second)
    (right : EquivalentOn U second third) :
    EquivalentOn U first third :=
  ⟨fun interpretation =>
      (left.pull_eq interpretation).trans (right.pull_eq interpretation),
    fun operationCost =>
      (left.pullCost_eq operationCost).trans
        (right.pullCost_eq operationCost)⟩

/-- Equivalent translations compile every circuit to the same semantics over
the observed carrier. -/
theorem compile_eval_eq
    {left right : Translation σ τ}
    (equivalent : EquivalentOn U left right)
    (circuit : Circuit σ n m)
    (interpretation : Interpretation τ U)
    (input : Fin n → U) :
    (left.compile circuit).eval interpretation input =
      (right.compile circuit).eval interpretation input := by
  rw [left.compile_eval, right.compile_eval,
    equivalent.pull_eq interpretation]

/-- Equivalent translations compile every circuit to the same weighted cost. -/
theorem compile_cost_eq
    {left right : Translation σ τ}
    (equivalent : EquivalentOn U left right)
    (circuit : Circuit σ n m)
    (operationCost : OperationCost τ) :
    (left.compile circuit).cost operationCost =
      (right.compile circuit).cost operationCost := by
  rw [left.compile_cost, right.compile_cost,
    equivalent.pullCost_eq operationCost]

end EquivalentOn

/-- Observational equivalence is a congruence for translation composition. -/
theorem comp_equivalentOn
    {outerLeft outerRight : Translation τ υ}
    {innerLeft innerRight : Translation σ τ}
    (outer : EquivalentOn U outerLeft outerRight)
    (inner : EquivalentOn U innerLeft innerRight) :
    EquivalentOn U (outerLeft.comp innerLeft) (outerRight.comp innerRight) where
  pull_eq := by
    intro interpretation
    rw [pull_comp, pull_comp, outer.pull_eq interpretation,
      inner.pull_eq (outerRight.pull interpretation)]
  pullCost_eq := by
    intro operationCost
    rw [pullCost_comp, pullCost_comp, outer.pullCost_eq operationCost,
      inner.pullCost_eq (outerRight.pullCost operationCost)]

/-- Left identity law, up to observational equivalence. -/
theorem id_comp_equivalentOn
    (translation : Translation σ τ) :
    EquivalentOn U ((Translation.id τ).comp translation) translation where
  pull_eq := by
    intro interpretation
    rw [pull_comp, pull_id]
  pullCost_eq := by
    intro operationCost
    rw [pullCost_comp, pullCost_id]

/-- Right identity law, up to observational equivalence. -/
theorem comp_id_equivalentOn
    (translation : Translation σ τ) :
    EquivalentOn U (translation.comp (Translation.id σ)) translation where
  pull_eq := by
    intro interpretation
    rw [pull_comp, pull_id]
  pullCost_eq := by
    intro operationCost
    rw [pullCost_comp, pullCost_id]

/-- Associativity law, up to observational equivalence. -/
theorem comp_assoc_equivalentOn
    (outer : Translation υ φ)
    (middle : Translation τ υ)
    (inner : Translation σ τ) :
    EquivalentOn U ((outer.comp middle).comp inner)
      (outer.comp (middle.comp inner)) where
  pull_eq := by
    intro interpretation
    rw [pull_comp, pull_comp, pull_comp, pull_comp]
  pullCost_eq := by
    intro operationCost
    rw [pullCost_comp, pullCost_comp, pullCost_comp, pullCost_comp]

/-- Setoid used to form the observational quotient of translations. -/
def equivalentOnSetoid (U : Type u) (σ τ : Signature) :
    Setoid (Translation σ τ) where
  r := EquivalentOn U
  iseqv :=
    { refl := EquivalentOn.refl
      symm := EquivalentOn.symm
      trans := EquivalentOn.trans }

end Translation

/-- A signature regarded as an object whose translations are observed over
the carrier `U`. -/
structure ObservedSignature (U : Type u) where
  /-- The underlying signature. -/
  signature : Signature

/-- A morphism of observed signatures is an observational equivalence class
of circuit translations. -/
def ObservedTranslation
    (U : Type u)
    (source target : ObservedSignature U) : Type _ :=
  Quotient (Translation.equivalentOnSetoid U source.signature target.signature)

namespace ObservedTranslation

/-- Include a raw translation in the observational quotient. -/
def mk
    {source target : ObservedSignature U}
    (translation : Translation source.signature target.signature) :
    ObservedTranslation U source target :=
  Quotient.mk _ translation

/-- Identity morphism in the observational quotient. -/
def id (signature : ObservedSignature U) :
    ObservedTranslation U signature signature :=
  mk (Translation.id signature.signature)

/-- Composition in the observational quotient. -/
def comp
    {source middle target : ObservedSignature U}
    (inner : ObservedTranslation U source middle)
    (outer : ObservedTranslation U middle target) :
    ObservedTranslation U source target :=
  Quotient.liftOn₂ inner outer
    (fun inner outer => mk (outer.comp inner))
    (by
      intro innerLeft outerLeft innerRight outerRight
        innerEquivalent outerEquivalent
      exact Quotient.sound <|
        Translation.comp_equivalentOn outerEquivalent innerEquivalent)

end ObservedTranslation

open CategoryTheory

/-- Circuit signatures and translations modulo semantic-and-cost observation
form a category. -/
instance (U : Type u) : Category (ObservedSignature U) where
  Hom := ObservedTranslation U
  id := ObservedTranslation.id
  comp := ObservedTranslation.comp
  id_comp := by
    intro source target morphism
    refine Quotient.inductionOn morphism ?_
    intro translation
    exact Quotient.sound (Translation.comp_id_equivalentOn translation)
  comp_id := by
    intro source target morphism
    refine Quotient.inductionOn morphism ?_
    intro translation
    exact Quotient.sound (Translation.id_comp_equivalentOn translation)
  assoc := by
    intro first second third fourth left middle right
    refine Quotient.inductionOn₃ left middle right ?_
    intro inner middle outer
    exact Quotient.sound
      (Translation.comp_assoc_equivalentOn outer middle inner).symm

end Algebraic
