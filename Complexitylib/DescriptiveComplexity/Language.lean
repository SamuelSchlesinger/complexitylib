/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding
public import Complexitylib.DescriptiveComplexity.Query
public import Complexitylib.Models.TuringMachine

/-!
# The language induced by a Boolean query

The bridge from descriptive complexity to the machine model: a Boolean query over
finite structures induces a **language** (a set of bit strings) — the encodings of
the structures satisfying it. This is where a logical characterization of a query
becomes a statement about a machine-model `Language`, the connection Fagin's
theorem (`NP = ∃SO`) and the other planned logic/complexity correspondences
ultimately rest on.

## Main definitions and results

- `DescriptiveComplexity.queryLanguage` — the language of a query.
- `DescriptiveComplexity.mem_queryLanguage` — a `Q`-satisfying structure's encoding
  is in `Q`'s language.
- `mem_queryLanguage_iff_decodeStruct` — exact membership via successful decoding.
- `encodeStruct_mem_queryLanguage_iff` — encoding preserves and reflects the query.
- `not_mem_queryLanguage_of_decodeStruct_eq_none` — malformed inputs are rejected.
-/


public section

namespace Complexity

namespace DescriptiveComplexity

variable {V : Vocabulary}

/-- The **language induced by a Boolean query** `Q`: the set of bit strings that
    encode a (decidable) structure satisfying `Q`. -/
def queryLanguage (Q : BooleanQuery V) : Language :=
  { x | ∃ A : DecFinStruct V, encodeStruct A = x ∧ Q A.toFinStruct }

/-- Encoding a `Q`-satisfying structure lands in `Q`'s induced language. -/
theorem mem_queryLanguage (Q : BooleanQuery V) (A : DecFinStruct V)
    (hQ : Q A.toFinStruct) : encodeStruct A ∈ queryLanguage Q :=
  ⟨A, rfl, hQ⟩

/-- Query-language membership is exactly successful decoding followed by the query. -/
theorem mem_queryLanguage_iff_decodeStruct (Q : BooleanQuery V) (bits : List Bool) :
    bits ∈ queryLanguage Q ↔
      ∃ A : DecFinStruct V, decodeStruct V bits = some A ∧ Q A.toFinStruct := by
  simp only [queryLanguage, Set.mem_ofPred_eq, decodeStruct_eq_some_iff]

/-- Encoding preserves and reflects the answer to any structural Boolean query. -/
theorem encodeStruct_mem_queryLanguage_iff (Q : BooleanQuery V) (A : DecFinStruct V) :
    encodeStruct A ∈ queryLanguage Q ↔ Q A.toFinStruct := by
  rw [mem_queryLanguage_iff_decodeStruct]
  simp

/-- A malformed encoding is outside every induced query language. -/
theorem not_mem_queryLanguage_of_decodeStruct_eq_none (Q : BooleanQuery V) (bits : List Bool)
    (h : decodeStruct V bits = none) : bits ∉ queryLanguage Q := by
  rw [mem_queryLanguage_iff_decodeStruct]
  simp only [h, reduceCtorEq, false_and, exists_false, not_false_eq_true]

end DescriptiveComplexity

end Complexity
