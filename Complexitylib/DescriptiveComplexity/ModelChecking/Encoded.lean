/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Language
public import Complexitylib.DescriptiveComplexity.ModelChecking

/-!
# First-order model checking on encoded inputs

Decode a structure and evaluate the sentence, rejecting every malformed string.
Correctness refers to the existing `queryLanguage`, so it includes all binary
inputs. `ModelChecking.PolynomialTime` proves that its one-bit verdict belongs
to the machine class `FP` for each fixed sentence.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Evaluate a sentence on an encoded structure, returning false on malformed input. -/
def Sentence.evalEncoded {V : Vocabulary} (φ : Sentence V) (bits : List Bool) : Bool :=
  match decodeStruct V bits with
  | none => false
  | some A => Sentence.evalB A φ

/-- The encoded evaluator rejects the unique length-zero input. -/
@[simp] theorem Sentence.evalEncoded_nil {V : Vocabulary} (φ : Sentence V) :
    φ.evalEncoded [] = false := by
  simp only [evalEncoded, decodeStruct_nil]

/-- The encoded evaluator recognizes exactly the sentence's induced binary language. -/
theorem Sentence.evalEncoded_eq_queryLanguage {V : Vocabulary} (φ : Sentence V)
    (bits : List Bool) :
    φ.evalEncoded bits = true ↔
      bits ∈ queryLanguage (fun A => Sentence.Models A φ) := by
  rw [mem_queryLanguage_iff_decodeStruct]
  cases hd : decodeStruct V bits with
  | none => simp [evalEncoded, hd]
  | some A => simp [evalEncoded, hd, Sentence.evalB_eq_models]

/-- On a valid encoding, encoded evaluation agrees with structure-level evaluation. -/
@[simp] theorem Sentence.evalEncoded_encodeStruct {V : Vocabulary} (φ : Sentence V)
    (A : DecFinStruct V) : φ.evalEncoded (encodeStruct A) = Sentence.evalB A φ := by
  simp only [evalEncoded, decodeStruct_encodeStruct]

end Complexity.DescriptiveComplexity
