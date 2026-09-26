/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Circuit.Validity.Defs
public import Complexitylib.DescriptiveComplexity.Circuit.Validity.Internal

/-!
# Validated first-order circuits

Encoding validity has depth at most three and exact size
`card + 4 + numConsts * (1 + card * (1 + card))`. Conjoining this test with the
sentence expansion gives exact query-language semantics on every input of the
chosen encoded length, including malformed strings.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- The validator accepts exactly the encodings at the chosen input length. -/
theorem encodingValidityFormula_correct (V : Vocabulary) (card : Nat)
    (input : BitString (encodingLength V card)) :
    (encodingValidityFormula V card).eval input = true ↔
      ∃ A : DecFinStruct V, encodeStruct A = List.ofFn input :=
  encodingValidityFormula_correct_internal V card input

/-- Encoding validation has an exact size polynomial of degree at most two. -/
theorem encodingValidityFormula_size (V : Vocabulary) (card : Nat) :
    (encodingValidityFormula V card).size = (encodingValidityPolynomial V).eval card :=
  encodingValidityFormula_size_internal V card

/-- Encoding validation has depth at most three, independently of universe size. -/
theorem encodingValidityFormula_depth (V : Vocabulary) (card : Nat) :
    (encodingValidityFormula V card).depth ≤ 3 := encodingValidityFormula_depth_internal V card

/-- Validated expansion recognizes the exact induced language at this encoded length. -/
theorem Sentence.validatedExpansion_correct {V : Vocabulary} (φ : Sentence V) (card : Nat)
    (input : BitString (encodingLength V card)) :
    (φ.validatedExpansion card).eval input = true ↔
      List.ofFn input ∈ queryLanguage (fun A => Sentence.Models A φ) :=
  validatedExpansion_correct_internal φ card input

/-- The complete validated expansion has exact polynomial size. -/
theorem Sentence.validatedExpansion_size {V : Vocabulary} (φ : Sentence V) (card : Nat) :
    (φ.validatedExpansion card).size = φ.validatedPolynomial.eval card :=
  validatedExpansion_size_internal φ card

/-- Validation adds only a constant number of depth layers to sentence expansion. -/
theorem Sentence.validatedExpansion_depth {V : Vocabulary} (φ : Sentence V) (card : Nat) :
    (φ.validatedExpansion card).depth ≤ φ.size + 4 := validatedExpansion_depth_internal φ card

/-- Actual circuit realizations decide the query on every input of the encoded length. -/
theorem Sentence.exists_validated_circuit {V : Vocabulary} (φ : Sentence V) (card : Nat) :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr (encodingLength V card) 1 gates,
      c.size = φ.validatedPolynomial.eval card ∧ c.depth ≤ φ.size + 5 ∧
        ∀ input, c.eval input 0 = true ↔
          List.ofFn input ∈ queryLanguage (fun A => Sentence.Models A φ) := by
  obtain ⟨gates, c, hsize, hdepth, heval⟩ := (φ.validatedExpansion card).exists_circuit
  refine ⟨gates, c, hsize.trans (φ.validatedExpansion_size card), ?_, ?_⟩
  · have := φ.validatedExpansion_depth card
    omega
  · intro input
    rw [heval input]
    exact φ.validatedExpansion_correct card input

end Complexity.DescriptiveComplexity
