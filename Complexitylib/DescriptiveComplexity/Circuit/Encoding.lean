/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Circuit
public import Complexitylib.DescriptiveComplexity.Encoding.Positions

/-!
# Circuit inputs in the existing structure encoding

The computable layout reads the exact positions in `encodeStruct`, including
the unary prefix offset. Unlike the abstract table numbering, it uses no
classical choice. Compilation now evaluates the actual encoded structures.
`Circuit.Validity` adds the constant-depth encoding check for arbitrary inputs.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Place relation and constant inputs at their actual encoded bit positions. -/
def encodingLayout (V : Vocabulary) (card : Nat) :
    StructureInput V card (encodingLength V card) where
  rel i args := ⟨encodingPosition V card (.inl ⟨i, args⟩), encodingPosition_lt V card _⟩
  const c a := ⟨encodingPosition V card (.inr (c, a)), encodingPosition_lt V card _⟩

/-- View the encoder's list as a circuit input at its exact encoded length. -/
def encodedInput {V : Vocabulary} (A : DecFinStruct V) : BitString (encodingLength V A.card) :=
  fun i => (encodeStruct A)[i.val]?.getD false

/-- Converting the circuit input vector to a list gives the original encoding exactly. -/
theorem ofFn_encodedInput {V : Vocabulary} (A : DecFinStruct V) :
    List.ofFn (encodedInput A) = encodeStruct A := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, encodeStruct_length_eq]
  · intro i hi hj
    simp only [List.getElem_ofFn, encodedInput, List.getElem?_eq_getElem hj, Option.getD_some]

/-- Every encoded structure supplies the relation and constant values required by compilation. -/
theorem encodedInput_represents {V : Vocabulary} (A : DecFinStruct V) :
    StructureInput.Represents A (encodingLayout V A.card) (encodedInput A) := by
  constructor <;> intros <;>
    simp [encodingLayout, encodedInput, getElem?_encodeStruct_position, inputSiteValue]

/-- The expansion reads the actual encoding correctly, for arbitrary open formulas. -/
theorem Formula.encoded_expansion_sat {V : Vocabulary} {n : Nat}
    (A : DecFinStruct V) (φ : Formula V n) (σ : Env A.card n) :
    ((encodingLayout V A.card).compile φ σ).eval (encodedInput A) = true ↔
      φ.Sat A.toFinStruct σ :=
  StructureInput.compile_sat A _ _ (encodedInput_represents A) φ σ

/-- The sentence expansion computes truth on the existing structure encoding. -/
theorem Sentence.encoded_expansion_models {V : Vocabulary} (A : DecFinStruct V)
    (φ : Sentence V) :
    ((encodingLayout V A.card).compile φ (emptyEnv A.card)).eval (encodedInput A) = true ↔
      Sentence.Models A.toFinStruct φ :=
  Formula.encoded_expansion_sat A φ (emptyEnv A.card)

/-- At every universe size, one circuit computes the expansion on all encoded-length inputs.
Correctness on encoded structures follows from `encoded_expansion_models`. -/
theorem Sentence.exists_encoding_circuit {V : Vocabulary} (φ : Sentence V) (card : Nat) :
    ∃ gates, ∃ c : Circuit Basis.unboundedAndOr (encodingLength V card) 1 gates,
      c.size = φ.expansionPolynomial.eval card ∧ c.depth ≤ φ.size + 2 ∧
        ∀ input, c.eval input 0 =
          ((encodingLayout V card).compile φ (emptyEnv card)).eval input :=
  (encodingLayout V card).exists_circuit φ (emptyEnv card)

end Complexity.DescriptiveComplexity
