/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation.Composition
public import Complexitylib.DescriptiveComplexity.Problem

/-!
# Reductions by tagged first-order interpretations

A reduction supplies a tagged full-product interpretation and a proof that it
preserves membership. Invariance of the target problem turns the composition
isomorphism into transitivity. The resulting reducibility relation is a preorder,
respects complement, and preserves first-order definability downwards.

This is the tagged version of the structural reductions in Immerman, Chapter 3,
and Senellart--Gnatenko (2026), Sections 3.1--3.2. It does not assert a resource
bound for a map on binary encodings, nor the restricted syntax of an exact
first-order projection.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

variable {U V W : Vocabulary}

/-- A first-order reduction with a fixed finite set of tags and a tuple dimension. -/
structure TaggedFOReduction (P : DecisionProblem V) (Q : DecisionProblem W) where
  /-- Number of disjoint copies of the tuple universe. -/
  tags : Nat
  /-- Number of source coordinates per target element. -/
  dim : Nat
  /-- The first-order interpretation producing the target structure. -/
  interpretation : TaggedFOInterpretation V W tags dim
  /-- The interpretation preserves and reflects membership. -/
  correct : ∀ A : FinStruct V, P A ↔ Q (interpretation.apply A)

namespace TaggedFOReduction

/-- The identity interpretation is a reduction of a problem to itself. -/
def refl (P : DecisionProblem V) : TaggedFOReduction P P where
  tags := 1
  dim := 1
  interpretation := TaggedFOInterpretation.idInterp V
  correct A := (P.invariant ⟨TaggedFOInterpretation.idIso A⟩).symm

/-- Compose reductions by flattening their tags and coordinate tuples. -/
def trans {P : DecisionProblem U} {Q : DecisionProblem V} {R : DecisionProblem W}
    (f : TaggedFOReduction P Q) (g : TaggedFOReduction Q R) : TaggedFOReduction P R where
  tags := g.tags * f.tags ^ g.dim
  dim := g.dim * f.dim
  interpretation := g.interpretation.comp f.interpretation
  correct A := (f.correct A).trans ((g.correct (f.interpretation.apply A)).trans
    (g.interpretation.comp_query f.interpretation A R.invariant).symm)

/-- The same interpretation reduces the two complementary problems. -/
def complement {P : DecisionProblem V} {Q : DecisionProblem W}
    (f : TaggedFOReduction P Q) : TaggedFOReduction P.complement Q.complement where
  tags := f.tags
  dim := f.dim
  interpretation := f.interpretation
  correct A := not_congr (f.correct A)

end TaggedFOReduction

/-- Reducibility by a tagged full-product first-order interpretation. -/
def TaggedFOReduces (P : DecisionProblem V) (Q : DecisionProblem W) : Prop :=
  Nonempty (TaggedFOReduction P Q)

/-- Tagged first-order reducibility is reflexive. -/
theorem TaggedFOReduces.refl (P : DecisionProblem V) : TaggedFOReduces P P :=
  ⟨TaggedFOReduction.refl P⟩

/-- Tagged first-order reducibility is transitive, even across vocabularies. -/
theorem TaggedFOReduces.trans {P : DecisionProblem U} {Q : DecisionProblem V}
    {R : DecisionProblem W} (h₁ : TaggedFOReduces P Q) (h₂ : TaggedFOReduces Q R) :
    TaggedFOReduces P R := by
  exact h₁.elim fun f => h₂.elim fun g => ⟨f.trans g⟩

/-- Tagged first-order reducibility respects complementation. -/
theorem TaggedFOReduces.complement {P : DecisionProblem V} {Q : DecisionProblem W}
    (h : TaggedFOReduces P Q) : TaggedFOReduces P.complement Q.complement := by
  exact h.map TaggedFOReduction.complement

/-- The preorder on problems over one vocabulary, available without a global order instance. -/
@[instance_reducible]
def TaggedFOReduces.preorder (V : Vocabulary) : Preorder (DecisionProblem V) where
  le := TaggedFOReduces
  le_refl := TaggedFOReduces.refl
  le_trans _ _ _ := TaggedFOReduces.trans

/-- Every universe-preserving reduction between invariant problems gives a tagged reduction. -/
theorem FOReduces.toTaggedFOReduces {P : DecisionProblem V} {Q : DecisionProblem W}
    (h : FOReduces P.toQuery Q.toQuery) : TaggedFOReduces P Q := by
  rcases h with ⟨I, hI⟩
  exact ⟨⟨1, 1, I.toTagged, fun A => (hI A).trans (I.toTagged_query A Q.invariant).symm⟩⟩

/-- FO definability is closed downwards under tagged first-order reductions. -/
theorem FODefinable.of_taggedReduces {P : DecisionProblem V} {Q : DecisionProblem W}
    (hQ : FODefinable Q.toQuery) (h : TaggedFOReduces P Q) : FODefinable P.toQuery := by
  rcases h with ⟨f⟩
  rcases hQ with ⟨φ, hφ⟩
  exact ⟨f.interpretation.translateSentence φ, fun A => (f.correct A).trans
    ((hφ (f.interpretation.apply A)).trans
      (f.interpretation.translateSentence_models A φ).symm)⟩

end Complexity.DescriptiveComplexity
