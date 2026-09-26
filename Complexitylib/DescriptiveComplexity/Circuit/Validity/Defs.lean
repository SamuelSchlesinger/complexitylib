/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Circuit.Encoding

/-!
# Constant-depth validation of structure encodings

Check the unary header and express each one-hot constant block as a disjunction
of its possible values. Relation bits are unrestricted. The outer conjunction
also checks the minimum universe size of two. The depth is at most three and
the size is quadratic in universe size for a fixed vocabulary.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Check the unary cardinality header, including its false terminator. -/
def encodingHeaderFormula (V : Vocabulary) (card : Nat) :
    AC0Formula (encodingLength V card) :=
  .andList ((List.finRange (card + 1)).map fun i =>
    .lit ⟨⟨i.val, by have := card_lt_encodingLength V card; omega⟩, decide (i.val < card)⟩)

/-- Assert that a constant block encodes exactly the specified element. -/
def constantValueFormula (V : Vocabulary) (card : Nat) (c : Fin V.numConsts)
    (a : Fin card) : AC0Formula (encodingLength V card) :=
  .andList ((List.finRange card).map fun b =>
    .lit ⟨(encodingLayout V card).const c b, decide (a = b)⟩)

/-- Validate the header, minimum universe size, and every one-hot constant block. -/
def encodingValidityFormula (V : Vocabulary) (card : Nat) :
    AC0Formula (encodingLength V card) :=
  .andList (.const (decide (2 ≤ card)) :: encodingHeaderFormula V card ::
    (List.finRange V.numConsts).map (fun c =>
      .orList ((List.finRange card).map (constantValueFormula V card c))))

/-- The exact tree size of the encoding validator as a natural-coefficient polynomial. -/
noncomputable def encodingValidityPolynomial (V : Vocabulary) : Polynomial Nat :=
  Polynomial.X + Polynomial.C 4 + Polynomial.C V.numConsts *
    (1 + Polynomial.X * (1 + Polynomial.X))

/-- Combine encoding validation with the finite expansion of a sentence. -/
def Sentence.validatedExpansion {V : Vocabulary} (φ : Sentence V) (card : Nat) :
    AC0Formula (encodingLength V card) :=
  .andList [encodingValidityFormula V card, (encodingLayout V card).compile φ (emptyEnv card)]

/-- Exact size polynomial for validation followed by sentence expansion. -/
noncomputable def Sentence.validatedPolynomial {V : Vocabulary} (φ : Sentence V) :
    Polynomial Nat := 1 + encodingValidityPolynomial V + φ.expansionPolynomial

end Complexity.DescriptiveComplexity
