/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Reduction.Encoding.Defs
public import Complexitylib.DescriptiveComplexity.SecondOrder.PolynomialTime
public import Complexitylib.Classes.NP.Closure
import Complexitylib.DescriptiveComplexity.Reduction.Encoding.Internal

/-!
# Structural first-order reductions give polynomial-time many-one reductions

The computable interpretation agrees exactly with the original structure map.
Its encoded map belongs to `FP`, outputs the complete target truth tables and
constant blocks, and sends malformed source strings to the non-encoding `[]`.
Consequently `FOReduces` induces the library's existing `MapReducesPoly` relation
on binary query languages, with no promise restricting the input strings.

Combining this bridge with Fagin's upper direction gives a completeness criterion:
an existential-SO target query is NP-complete if an NP-hard encoded query reduces
to it by an existing universe-preserving FO interpretation. This implements the
structural reduction method of Immerman's *Descriptive Complexity*, Chapter 3.
The tagged tuple encoding bridge and exact first-order projections remain separate.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Computable interpretation represents the original propositional structure map exactly. -/
@[simp] theorem FOInterpretation.applyDec_toFinStruct {V W : Vocabulary}
    (I : FOInterpretation V W) (A : DecFinStruct V) :
    (I.applyDec A).toFinStruct = I.apply A.toFinStruct := applyDec_toFinStruct_internal I A

/-- Arithmetic generation yields precisely the interpreted structure's encoding. -/
theorem FOInterpretation.rawEncoding_encodeStruct {V W : Vocabulary}
    (I : FOInterpretation V W) (A : DecFinStruct V) :
    I.rawEncoding A.card (encodeStruct A) = encodeStruct (I.applyDec A) :=
  rawEncoding_encodeStruct_internal I A

/-- The raw output includes the header, every target relation table, and every constant block. -/
@[simp] theorem FOInterpretation.rawEncoding_length {V W : Vocabulary}
    (I : FOInterpretation V W) (card : Nat) (input : List Bool) :
    (I.rawEncoding card input).length = encodingLength W card :=
  rawEncoding_length_internal I card input

/-- Arithmetic table generation is polynomial-time on polynomial-time supplied input and size. -/
theorem FOInterpretation.rawEncoding_mem_FP {V W : Vocabulary} (I : FOInterpretation V W)
    {input : List Bool → List Bool} {card : List Bool → Nat}
    (hinput : input ∈ FP) (hcard : UnaryFn card) :
    (fun z => I.rawEncoding (card z) (input z)) ∈ FP := rawEncoding_mem_FP_internal I hinput hcard

/-- On valid encodings, the binary map applies the interpretation and re-encodes its output. -/
@[simp] theorem FOInterpretation.mapEncoding_encodeStruct {V W : Vocabulary}
    (I : FOInterpretation V W) (A : DecFinStruct V) :
    I.mapEncoding (encodeStruct A) = encodeStruct (I.applyDec A) := by
  simp only [mapEncoding, decodeStruct_encodeStruct]

/-- Every malformed source encoding maps to the empty string. -/
theorem FOInterpretation.mapEncoding_of_decode_eq_none {V W : Vocabulary}
    (I : FOInterpretation V W) (input : List Bool) (h : decodeStruct V input = none) :
    I.mapEncoding input = [] := by simp only [mapEncoding, h]

/-- In particular, an interpretation's binary map preserves the fixed malformed input `[]`. -/
@[simp] theorem FOInterpretation.mapEncoding_nil {V W : Vocabulary}
    (I : FOInterpretation V W) : I.mapEncoding [] = [] := by simp [mapEncoding]

/-- A valid input produces the full encoded target length at the same universe cardinality. -/
theorem FOInterpretation.mapEncoding_length_encodeStruct {V W : Vocabulary}
    (I : FOInterpretation V W) (A : DecFinStruct V) :
    (I.mapEncoding (encodeStruct A)).length = encodingLength W A.card := by
  rw [mapEncoding_encodeStruct, encodeStruct_length_eq]
  rfl

/-- The full output length is bounded by the target encoding polynomial in input length. -/
theorem FOInterpretation.mapEncoding_length_le {V W : Vocabulary}
    (I : FOInterpretation V W) (input : List Bool) :
    (I.mapEncoding input).length ≤ encodingLength W input.length := by
  cases hd : decodeStruct V input with
  | none => simp [I.mapEncoding_of_decode_eq_none input hd]
  | some A =>
    obtain rfl := (decodeStruct_eq_some_iff input A).mp hd
    rw [mapEncoding_length_encodeStruct]
    apply (encodingLength_strictMono W).monotone
    rw [encodeStruct_length_eq]
    exact (card_lt_encodingLength V A.card).le

/-- Every fixed universe-preserving FO interpretation gives an actual polynomial-time string map. -/
theorem FOInterpretation.mapEncoding_mem_FP {V W : Vocabulary} (I : FOInterpretation V W) :
    I.mapEncoding ∈ FP := mapEncoding_mem_FP_internal I

/-- The binary map pulls query languages back exactly, including every malformed input. -/
theorem FOInterpretation.mapEncoding_mem_queryLanguage_iff {V W : Vocabulary}
    (I : FOInterpretation V W) (Q : BooleanQuery W) (input : List Bool) :
    I.mapEncoding input ∈ queryLanguage Q ↔
      input ∈ queryLanguage (fun A => Q (I.apply A)) :=
  mapEncoding_mem_queryLanguage_iff_internal I Q input

/-- Structural FO reducibility induces polynomial-time many-one reducibility on binary languages. -/
theorem FOReduces.mapReducesPoly {V W : Vocabulary} {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (h : FOReduces Q₁ Q₂) : queryLanguage Q₁ ≤ₚ queryLanguage Q₂ := by
  obtain ⟨I, hI⟩ := h
  refine ⟨I.mapEncoding, I.mapEncoding_mem_FP, fun input => ?_⟩
  rw [I.mapEncoding_mem_queryLanguage_iff]
  simp only [mem_queryLanguage_iff_decodeStruct, hI]

/-- The legacy quantifier-free interpretation reductions also induce polynomial-time reductions. -/
theorem FOProjReduces.mapReducesPoly {V W : Vocabulary} {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (h : FOProjReduces Q₁ Q₂) : queryLanguage Q₁ ≤ₚ queryLanguage Q₂ := h.toFOReduces.mapReducesPoly

/-- Machine P membership transports backward along structural FO reductions. -/
theorem FOReduces.queryLanguage_mem_P {V W : Vocabulary} {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (h : FOReduces Q₁ Q₂) (hQ₂ : queryLanguage Q₂ ∈ P) : queryLanguage Q₁ ∈ P :=
  h.mapReducesPoly.mem_P hQ₂

/-- Machine NP membership transports backward along structural FO reductions. -/
theorem FOReduces.queryLanguage_mem_NP {V W : Vocabulary}
    {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (h : FOReduces Q₁ Q₂) (hQ₂ : queryLanguage Q₂ ∈ NP) : queryLanguage Q₁ ∈ NP :=
  h.mapReducesPoly.mem_NP hQ₂

/-- An ESO target is NP-complete when an NP-hard encoded query FO-reduces to it. -/
theorem ExistSODefinable.npComplete_of_foReduces {V W : Vocabulary}
    {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W} (hQ₂ : ExistSODefinable Q₂)
    (hhard : NPHard (queryLanguage Q₁)) (hred : FOReduces Q₁ Q₂) :
    NPComplete (queryLanguage Q₂) :=
  NPComplete.of_mem_of_reduction hhard hQ₂.queryLanguage_mem_NP hred.mapReducesPoly

end Complexity.DescriptiveComplexity
