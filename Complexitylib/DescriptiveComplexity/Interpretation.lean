/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation.Defs
public import Complexitylib.DescriptiveComplexity.FirstOrder.Isomorphism

/-!
# Tagged tuple interpretation semantics

Tagged FO interpretations have exact output size `tags * card ^ dim` and preserve
isomorphisms. Consequently, pulling a query back through their structure map
preserves isomorphism invariance. A two-copy graph construction demonstrates that
this extends the expressive scope of universe-preserving interpretations.

`Interpretation.Pullback` proves general formula transport and closure of FO
definability. `Interpretation.Composition` gives composition up to isomorphism,
and `TaggedReduction` derives the reduction preorder on invariant problems.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

namespace TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim : Nat}

/-- The interpreted universe has exactly `tags * card ^ dim` elements. -/
@[simp] theorem apply_card (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V) :
    (I.apply A).card = tags * A.card ^ dim := rfl

/-- Map the coordinates of an interpreted element, keeping its tag. -/
def mapElement {card₁ card₂ : Nat} (f : Fin card₁ → Fin card₂)
    (x : Fin (tags * card₁ ^ dim)) : Fin (tags * card₂ ^ dim) :=
  (elementEquiv card₂ tags dim).symm
    ((elementEquiv card₁ tags dim x).1, f ∘ (elementEquiv card₁ tags dim x).2)

/-- Decoding a mapped element exposes its unchanged tag and mapped coordinates. -/
@[simp] theorem elementEquiv_mapElement {card₁ card₂ : Nat}
    (f : Fin card₁ → Fin card₂) (x : Fin (tags * card₁ ^ dim)) :
    elementEquiv card₂ tags dim (mapElement f x) =
      ((elementEquiv card₁ tags dim x).1, f ∘ (elementEquiv card₁ tags dim x).2) := by
  simp [mapElement]

/-- Coordinate mapping commutes with flattening relation arguments. -/
theorem relationEnv_mapElement {card₁ card₂ arity : Nat} (f : Fin card₁ → Fin card₂)
    (args : Fin arity → Fin (tags * card₁ ^ dim)) :
    relationEnv (mapElement f ∘ args) = f ∘ relationEnv args := by
  funext k
  simp [relationEnv, Function.comp_def]

/-- An input isomorphism acts coordinatewise on tagged tuples. -/
def mapIso (I : TaggedFOInterpretation V W tags dim) {A B : FinStruct V}
    (f : Iso A B) : Iso (I.apply A) (I.apply B) where
  toFun := mapElement f.toFun
  invFun := mapElement f.invFun
  left_inv x := by
    change Fin (tags * A.card ^ dim) at x
    apply (elementEquiv A.card tags dim).injective
    simp [Function.comp_def, f.left_inv]
  right_inv x := by
    change Fin (tags * B.card ^ dim) at x
    apply (elementEquiv B.card tags dim).injective
    simp [Function.comp_def, f.right_inv]
  rel_map i args := by
    change Fin (W.relArity i) → Fin (tags * A.card ^ dim) at args
    change (I.relFormula i _).Sat A (relationEnv args) ↔
      (I.relFormula i (fun j =>
        (elementEquiv B.card tags dim (mapElement f.toFun (args j))).1)).Sat B
        (relationEnv (mapElement f.toFun ∘ args))
    simp only [elementEquiv_mapElement]
    rw [relationEnv_mapElement]
    exact Formula.sat_iso f _ _
  const_map c := by
    apply (elementEquiv B.card tags dim).injective
    simp [Function.comp_def, f.const_map]

/-- Pull back a query along the tagged structure map. -/
def pullQuery (I : TaggedFOInterpretation V W tags dim) (Q : BooleanQuery W) :
    BooleanQuery V := fun A => Q (I.apply A)

/-- Isomorphism-invariant queries remain invariant under tagged interpretation. -/
theorem pullQuery_orderIndependent (I : TaggedFOInterpretation V W tags dim)
    {Q : BooleanQuery W} (hQ : Q.IsOrderIndependent) : (I.pullQuery Q).IsOrderIndependent := by
  rintro A B ⟨f⟩
  exact hQ ⟨I.mapIso f⟩

end TaggedFOInterpretation

/-- Regard a universe-preserving interpretation as a one-tag, one-coordinate interpretation. -/
def FOInterpretation.toTagged {V W : Vocabulary} (I : FOInterpretation V W) :
    TaggedFOInterpretation V W 1 1 where
  tags_pos := by decide
  dim_pos := by decide
  relFormula := fun i _ => (I.relFormula i).subst
    (fun j => .var (finProdFinEquiv (j, 0)))
  constTag := fun _ => 0
  constCoord := fun c _ => I.constMap c

open TaggedFOInterpretation in
/-- The old and new presentations of a dimension-one interpretation are isomorphic. -/
def FOInterpretation.toTaggedIso {V W : Vocabulary} (I : FOInterpretation V W)
    (A : FinStruct V) : Iso (I.toTagged.apply A) (I.apply A) where
  toFun := fun x => (elementEquiv A.card 1 1 x).2 0
  invFun := fun x => (elementEquiv A.card 1 1).symm (0, fun _ => x)
  left_inv x := by
    apply (elementEquiv A.card 1 1).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · funext i; exact congrArg ((elementEquiv A.card 1 1 x).2) (Subsingleton.elim 0 i)
  right_inv x := by
    simp
  rel_map i args := by
    change Formula.Sat A (relationEnv args) ((I.relFormula i).subst _) ↔ _
    rw [Formula.subst_sat]
    simp only [relationEnv, Term.eval, Equiv.symm_apply_apply, FOInterpretation.apply]
    rfl
  const_map c := by
    simp [FOInterpretation.toTagged, FOInterpretation.apply]

/-- An invariant query sees the same result through either dimension-one presentation. -/
theorem FOInterpretation.toTagged_query {V W : Vocabulary} (I : FOInterpretation V W)
    (A : FinStruct V) {Q : BooleanQuery W} (hQ : Q.IsOrderIndependent) :
    Q (I.toTagged.apply A) ↔ Q (I.apply A) := hQ ⟨I.toTaggedIso A⟩

end Complexity.DescriptiveComplexity
