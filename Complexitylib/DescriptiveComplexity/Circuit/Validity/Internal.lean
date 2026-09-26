/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Circuit.Validity.Defs
public import Complexitylib.DescriptiveComplexity.Language

/-!
# Proofs for encoding validation

Literal tests characterize the header and one-hot blocks. Encoding
reconstruction proves completeness of these tests; finite connective laws
account for size and depth.
-/

public section

namespace Complexity.DescriptiveComplexity

private theorem literal_eval_eq_true {N : Nat} (wire : Fin N) (polarity : Bool)
    (input : BitString N) :
    (AC0Formula.lit ⟨wire, polarity⟩).eval input = true ↔ input wire = polarity := by
  cases polarity <;> simp [AC0Formula.eval, Literal.eval]

theorem encodingHeaderFormula_eval_internal (V : Vocabulary) (card : Nat)
    (input : BitString (encodingLength V card)) :
    (encodingHeaderFormula V card).eval input = true ↔
      ∀ i : Fin (card + 1), input ⟨i.val, by
        have := card_lt_encodingLength V card; omega⟩ = decide (i.val < card) := by
  simp [encodingHeaderFormula, AC0Formula.eval_andList, List.all_eq_true,
    literal_eval_eq_true]

theorem constantValueFormula_eval_internal (V : Vocabulary) (card : Nat)
    (c : Fin V.numConsts) (a : Fin card) (input : BitString (encodingLength V card)) :
    (constantValueFormula V card c a).eval input = true ↔
      ∀ b, input ((encodingLayout V card).const c b) = decide (a = b) := by
  simp [constantValueFormula, AC0Formula.eval_andList, List.all_eq_true,
    literal_eval_eq_true]

theorem encodingValidityFormula_eval_internal (V : Vocabulary) (card : Nat)
    (input : BitString (encodingLength V card)) :
    (encodingValidityFormula V card).eval input = true ↔
      2 ≤ card ∧
      (∀ i : Fin (card + 1), input ⟨i.val, by
        have := card_lt_encodingLength V card; omega⟩ = decide (i.val < card)) ∧
      ∀ c, ∃ a : Fin card,
        ∀ b, input ((encodingLayout V card).const c b) = decide (a = b) := by
  simp [encodingValidityFormula, AC0Formula.eval_andList, AC0Formula.eval_orList,
    List.all_eq_true, List.any_eq_true, encodingHeaderFormula_eval_internal,
    constantValueFormula_eval_internal, AC0Formula.eval]

private theorem getElem?_ofFn_wire {N : Nat} (input : BitString N) (i : Fin N) :
    (List.ofFn input)[i.val]? = some (input i) := by simp

private theorem card_eq_of_encoding {V : Vocabulary} {card : Nat} (A : DecFinStruct V)
    (input : BitString (encodingLength V card)) (h : encodeStruct A = List.ofFn input) :
    A.card = card := by
  apply (encodingLength_strictMono V).injective
  simpa only [encodeStruct_length_eq, List.length_ofFn] using congrArg List.length h

private theorem input_eq_of_encoding {V : Vocabulary} (A : DecFinStruct V)
    (input : BitString (encodingLength V A.card)) (h : encodeStruct A = List.ofFn input) :
    encodedInput A = input := by
  funext i
  have hi := congrArg (fun bits => bits[i.val]?.getD false) h
  simpa only [encodedInput, getElem?_ofFn_wire, Option.getD_some] using hi

theorem encodingValidityFormula_encoded_internal {V : Vocabulary} (A : DecFinStruct V) :
    (encodingValidityFormula V A.card).eval (encodedInput A) = true := by
  apply (encodingValidityFormula_eval_internal V A.card _).mpr
  refine ⟨A.hcard, ?_, fun c => ⟨A.const c, (encodedInput_represents A).2 c⟩⟩
  intro i
  change (encodeStruct A)[i.val]?.getD false = _
  rw [getElem?_encodeStruct_header]
  rfl

theorem encodingValidityFormula_correct_internal (V : Vocabulary) (card : Nat)
    (input : BitString (encodingLength V card)) :
    (encodingValidityFormula V card).eval input = true ↔
      ∃ A : DecFinStruct V, encodeStruct A = List.ofFn input := by
  constructor
  · intro h
    obtain ⟨hcard, hheader, hconst⟩ := (encodingValidityFormula_eval_internal V card input).mp h
    choose values hvalues using hconst
    let A : DecFinStruct V :=
      ⟨card, hcard, (fun i args => input ((encodingLayout V card).rel i args)), values⟩
    refine ⟨A, encodeStruct_eq_of_values A (List.ofFn input) ?_ ?_ ?_⟩
    · exact List.length_ofFn
    · intro i
      exact (getElem?_ofFn_wire input ⟨i.val, by
        have := card_lt_encodingLength V card
        have hi : i.val < card + 1 := i.isLt
        omega⟩).trans
        (congrArg some (hheader i))
    · rintro (⟨i, args⟩ | ⟨c, a⟩)
      · exact getElem?_ofFn_wire input ((encodingLayout V card).rel i args)
      · exact (getElem?_ofFn_wire input ((encodingLayout V card).const c a)).trans
          (congrArg some (hvalues c a))
  · rintro ⟨A, hA⟩
    have hcard := card_eq_of_encoding A input hA
    subst card
    rw [← input_eq_of_encoding A input hA]
    exact encodingValidityFormula_encoded_internal A

private theorem header_size (V : Vocabulary) (card : Nat) :
    (encodingHeaderFormula V card).size = card + 2 := by
  simp [encodingHeaderFormula, AC0Formula.size_andList, List.map_map,
    Function.comp_def, AC0Formula.size, Nat.add_left_comm]

private theorem value_size (V : Vocabulary) (card : Nat) (c : Fin V.numConsts)
    (a : Fin card) : (constantValueFormula V card c a).size = 1 + card := by
  simp [constantValueFormula, AC0Formula.size_andList, List.map_map,
    Function.comp_def, AC0Formula.size]

theorem encodingValidityFormula_size_internal (V : Vocabulary) (card : Nat) :
    (encodingValidityFormula V card).size = (encodingValidityPolynomial V).eval card := by
  simp [encodingValidityFormula, AC0Formula.size_andList, AC0Formula.size_orList,
    List.map_map, Function.comp_def, header_size, value_size, AC0Formula.size,
    encodingValidityPolynomial]
  omega

private theorem header_depth (V : Vocabulary) (card : Nat) :
    (encodingHeaderFormula V card).depth ≤ 1 := by
  apply AC0Formula.depth_andList_le _ 0
  intro f hf
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
  exact Nat.le_refl 0

private theorem value_depth (V : Vocabulary) (card : Nat) (c : Fin V.numConsts)
    (a : Fin card) : (constantValueFormula V card c a).depth ≤ 1 := by
  apply AC0Formula.depth_andList_le _ 0
  intro f hf
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
  exact Nat.le_refl 0

theorem encodingValidityFormula_depth_internal (V : Vocabulary) (card : Nat) :
    (encodingValidityFormula V card).depth ≤ 3 := by
  apply AC0Formula.depth_andList_le _ 2
  intro f hf
  simp only [List.mem_cons] at hf
  rcases hf with rfl | rfl | hf
  · exact Nat.zero_le _
  · exact (header_depth V card).trans (by omega)
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hf
    apply AC0Formula.depth_orList_le _ 1
    intro f hf
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
    exact value_depth V card c a

theorem validatedExpansion_correct_internal {V : Vocabulary} (φ : Sentence V) (card : Nat)
    (input : BitString (encodingLength V card)) :
    (φ.validatedExpansion card).eval input = true ↔
      List.ofFn input ∈ queryLanguage (fun A => Sentence.Models A φ) := by
  simp only [Sentence.validatedExpansion, AC0Formula.eval_andList, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true]
  constructor
  · rintro ⟨hvalid, hφ⟩
    obtain ⟨A, hA⟩ := (encodingValidityFormula_correct_internal V card input).mp hvalid
    have hcard := card_eq_of_encoding A input hA
    subst card
    rw [← input_eq_of_encoding A input hA] at hφ
    rw [← hA]
    exact mem_queryLanguage _ A ((Sentence.encoded_expansion_models A φ).mp hφ)
  · intro h
    obtain ⟨A, hA, hφ⟩ := (mem_queryLanguage_iff_decodeStruct _ _).mp h
    have he := (decodeStruct_eq_some_iff _ _).mp hA
    have hcard := card_eq_of_encoding A input he
    subst card
    rw [← input_eq_of_encoding A input he]
    exact ⟨encodingValidityFormula_encoded_internal A,
      (Sentence.encoded_expansion_models A φ).mpr hφ⟩

theorem validatedExpansion_size_internal {V : Vocabulary} (φ : Sentence V) (card : Nat) :
    (φ.validatedExpansion card).size = φ.validatedPolynomial.eval card := by
  simp [Sentence.validatedExpansion, AC0Formula.size_andList,
    encodingValidityFormula_size_internal, StructureInput.compile_size,
    Sentence.validatedPolynomial, Nat.add_assoc]

theorem validatedExpansion_depth_internal {V : Vocabulary} (φ : Sentence V) (card : Nat) :
    (φ.validatedExpansion card).depth ≤ φ.size + 4 := by
  apply AC0Formula.depth_andList_le _ (φ.size + 3)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact (encodingValidityFormula_depth_internal V card).trans (by omega)
  · have := (encodingLayout V card).compile_depth φ (emptyEnv card)
    omega

end Complexity.DescriptiveComplexity
