/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation.Composition.Defs
public import Complexitylib.DescriptiveComplexity.Interpretation.Pullback.Internal

/-!
# Correctness of tagged interpretation composition

Flattening tags and coordinates is a bijection. Under that bijection, the
coordinate environment for the composite agrees with the environment obtained
by two successive interpretations. The pullback theorem supplies relation
preservation.
-/

public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {U V W : Vocabulary} {t₁ d₁ t₂ d₂ : Nat}

theorem flatten_unflatten (card t₁ d₁ t₂ d₂ : Nat)
    (x : Fin ((t₂ * t₁ ^ d₂) * card ^ (d₂ * d₁))) :
    flattenElement card t₁ d₁ t₂ d₂ (unflattenElement card t₁ d₁ t₂ d₂ x) = x := by
  apply (elementEquiv card (t₂ * t₁ ^ d₂) (d₂ * d₁)).injective
  simp only [flattenElement, unflattenElement, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    Prod.mk.eta]

theorem unflatten_flatten (card t₁ d₁ t₂ d₂ : Nat)
    (x : Fin (t₂ * (t₁ * card ^ d₁) ^ d₂)) :
    unflattenElement card t₁ d₁ t₂ d₂ (flattenElement card t₁ d₁ t₂ d₂ x) = x := by
  apply (elementEquiv (t₁ * card ^ d₁) t₂ d₂).injective
  simp only [flattenElement, unflattenElement, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    Prod.mk.eta]

theorem comp_coordEnv (A : FinStruct U) {arity : Nat}
    (args : Fin arity → Fin ((t₂ * t₁ ^ d₂) * A.card ^ (d₂ * d₁))) :
    coordEnv A (compTags (fun j => (elementEquiv A.card _ _ (args j)).1))
      (compCoords U arity d₁ d₂) (relationEnv args) =
        relationEnv (unflattenElement A.card t₁ d₁ t₂ d₂ ∘ args) := by
  funext ij
  simp [coordEnv, compTags, compCoords, relationEnv, unflattenElement, Term.eval]

/-- The composite and successive interpretations agree up to their canonical presentation. -/
def compIso (I₂ : TaggedFOInterpretation V W t₂ d₂) (I₁ : TaggedFOInterpretation U V t₁ d₁)
    (A : FinStruct U) : Iso ((I₂.comp I₁).apply A) (I₂.apply (I₁.apply A)) where
  toFun := unflattenElement A.card t₁ d₁ t₂ d₂
  invFun := flattenElement A.card t₁ d₁ t₂ d₂
  left_inv := flatten_unflatten A.card t₁ d₁ t₂ d₂
  right_inv := unflatten_flatten A.card t₁ d₁ t₂ d₂
  rel_map i args := by
    change Formula.Sat A (relationEnv args) (I₁.pullbackWith _ _ _) ↔ _
    rw [pullbackWith_sat, comp_coordEnv]
    change _ ↔ (I₂.relFormula i _).Sat (I₁.apply A) _
    simp only [Function.comp_apply, unflattenElement, Equiv.apply_symm_apply]
  const_map c := by
    simp only [apply, comp, unflattenElement, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

end Complexity.DescriptiveComplexity.TaggedFOInterpretation
