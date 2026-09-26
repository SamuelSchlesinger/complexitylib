/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation.Pullback.Defs

/-!
# Composition of tagged interpretations

Composing `(t₁, d₁)` with `(t₂, d₂)` gives tag count `t₂ * t₁ ^ d₂`
and dimension `d₂ * d₁`. A composite tag records an outer tag and one inner
tag for each outer coordinate. Coordinates are flattened with `finProdFinEquiv`.
The outer relation formulas are pulled back through the inner interpretation.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {U V W : Vocabulary} {t₁ d₁ t₂ d₂ : Nat}

/-- Expand composite tags to the tags of the inner elements of each argument. -/
def compTags {arity : Nat} (τ : Fin arity → Fin (t₂ * t₁ ^ d₂)) :
    Fin (arity * d₂) → Fin t₁ := fun ij =>
  (elementEquiv t₁ t₂ d₂ (τ (finProdFinEquiv.symm ij).1)).2 (finProdFinEquiv.symm ij).2

/-- Source variables for the inner coordinates, in flattened argument-coordinate order. -/
def compCoords (U : Vocabulary) (arity d₁ d₂ : Nat) :
    Fin (arity * d₂) → Fin d₁ → Term U (arity * (d₂ * d₁)) := fun ij k =>
  .var (finProdFinEquiv ((finProdFinEquiv.symm ij).1,
    finProdFinEquiv ((finProdFinEquiv.symm ij).2, k)))

/-- Compose tagged interpretations, recording all inner tags in the composite tag. -/
def comp (I₂ : TaggedFOInterpretation V W t₂ d₂) (I₁ : TaggedFOInterpretation U V t₁ d₁) :
    TaggedFOInterpretation U W (t₂ * t₁ ^ d₂) (d₂ * d₁) where
  tags_pos := Nat.mul_pos I₂.tags_pos (Nat.pow_pos I₁.tags_pos)
  dim_pos := Nat.mul_pos I₂.dim_pos I₁.dim_pos
  relFormula := fun i τ =>
    I₁.pullbackWith (I₂.relFormula i (fun j => (elementEquiv t₁ t₂ d₂ (τ j)).1))
      (compTags τ) (compCoords U (W.relArity i) d₁ d₂)
  constTag := fun c => (elementEquiv t₁ t₂ d₂).symm
    (I₂.constTag c, fun j => I₁.constTag (I₂.constCoord c j))
  constCoord := fun c jk =>
    I₁.constCoord (I₂.constCoord c (finProdFinEquiv.symm jk).1) (finProdFinEquiv.symm jk).2

/-- Decode a composite element as an outer element whose coordinates are inner elements. -/
def unflattenElement (card t₁ d₁ t₂ d₂ : Nat)
    (x : Fin ((t₂ * t₁ ^ d₂) * card ^ (d₂ * d₁))) : Fin (t₂ * (t₁ * card ^ d₁) ^ d₂) :=
  let p := elementEquiv card (t₂ * t₁ ^ d₂) (d₂ * d₁) x
  let tag := elementEquiv t₁ t₂ d₂ p.1
  (elementEquiv (t₁ * card ^ d₁) t₂ d₂).symm
    (tag.1, fun j => (elementEquiv card t₁ d₁).symm
      (tag.2 j, fun k => p.2 (finProdFinEquiv (j, k))))

/-- Flatten an outer element, retaining every inner tag and coordinate. -/
def flattenElement (card t₁ d₁ t₂ d₂ : Nat)
    (x : Fin (t₂ * (t₁ * card ^ d₁) ^ d₂)) : Fin ((t₂ * t₁ ^ d₂) * card ^ (d₂ * d₁)) :=
  let p := elementEquiv (t₁ * card ^ d₁) t₂ d₂ x
  (elementEquiv card (t₂ * t₁ ^ d₂) (d₂ * d₁)).symm
    ((elementEquiv t₁ t₂ d₂).symm (p.1, fun j => (elementEquiv card t₁ d₁ (p.2 j)).1),
      fun jk => (elementEquiv card t₁ d₁ (p.2 (finProdFinEquiv.symm jk).1)).2
        (finProdFinEquiv.symm jk).2)

end Complexity.DescriptiveComplexity.TaggedFOInterpretation
