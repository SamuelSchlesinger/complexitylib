/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Reduction
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Tagged tuple interpretations: definitions

A `TaggedFOInterpretation V W tags dim` defines a target structure on the full
universe `Fin tags × (Fin dim → Fin A.card)`. Tags supply disjoint copies without
using a built-in order. The target is presented on `Fin (tags * A.card ^ dim)` by
Mathlib's finite product and tuple equivalences. Its size is exact.

Both the tag count and dimension are positive, so our convention `card ≥ 2` is
preserved. Target constants are tagged tuples of source constants. There are no
domain restrictions or quotients. This module supplies the structure map;
`Interpretation.Pullback` and `Interpretation.Composition` develop its logical
transport and composition laws.

The tagged full-universe design follows Senellart and Gnatenko (2026), Sections
2.3 and 3.2, <https://arxiv.org/abs/2609.18261>. This implementation uses our finite
vocabularies, de Bruijn formulas, and `FinStruct` presentation.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- An FO interpretation whose elements are tagged tuples of source elements. -/
structure TaggedFOInterpretation (V W : Vocabulary) (tags dim : Nat) where
  /-- At least one disjoint copy of the tuple universe is present. -/
  tags_pos : 0 < tags
  /-- Positive dimension preserves our minimum universe size. -/
  dim_pos : 0 < dim
  /-- Each target relation is defined for each assignment of tags to its arguments. -/
  relFormula : (i : Fin W.numRels) → (Fin (W.relArity i) → Fin tags) →
    Formula V (W.relArity i * dim)
  /-- The tag of each target constant. -/
  constTag : Fin W.numConsts → Fin tags
  /-- Each coordinate of a target constant is a source constant. -/
  constCoord : Fin W.numConsts → Fin dim → Fin V.numConsts

namespace TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim : Nat}

/-- Decode the canonical finite presentation into a tag and a tuple. -/
def elementEquiv (card tags dim : Nat) :
    Fin (tags * card ^ dim) ≃ Fin tags × (Fin dim → Fin card) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv.symm)

/-- Flatten a tuple of interpreted elements into the environment for a relation formula. -/
def relationEnv {card arity : Nat} (args : Fin arity → Fin (tags * card ^ dim)) :
    Env card (arity * dim) := fun k =>
  (elementEquiv card tags dim (args (finProdFinEquiv.symm k).1)).2
    (finProdFinEquiv.symm k).2

/-- The full interpreted universe still has at least two elements. -/
theorem two_le_card (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V) :
    2 ≤ tags * A.card ^ dim := by
  exact A.hcard.trans ((Nat.le_pow I.dim_pos).trans
    (Nat.le_mul_of_pos_left _ I.tags_pos))

/-- Apply a tagged interpretation, using the full product universe. The abbreviation
keeps the cardinality visible when transporting dependent variable environments. -/
abbrev apply (I : TaggedFOInterpretation V W tags dim) (A : FinStruct V) : FinStruct W where
  card := tags * A.card ^ dim
  hcard := I.two_le_card A
  rel := fun i args => (I.relFormula i (fun j => (elementEquiv A.card tags dim (args j)).1)).Sat
    A (relationEnv args)
  const := fun c => (elementEquiv A.card tags dim).symm
    (I.constTag c, fun j => A.const (I.constCoord c j))

end TaggedFOInterpretation

end Complexity.DescriptiveComplexity
