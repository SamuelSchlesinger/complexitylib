/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.TaggedReduction.Encoding.Defs
import Complexitylib.DescriptiveComplexity.TaggedReduction.Encoding.Internal

/-!
# Exact encoded semantics for tagged interpretations

Arithmetic tag and coordinate extraction agrees with the original finite
equivalences. Generating the relation tables and packed constants therefore
produces exactly the interpreted structure's encoding, of length
`encodingLength W (tags * card ^ dim)`.

The decoder-based map rejects malformed inputs. Its polynomial-time machine
bound remains to be proved; this module is the semantic checkpoint for that bridge.
-/

public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim : Nat}

/-- The tag occupies the quotient above the full tuple block. -/
theorem elementEquiv_tag_val {card : Nat} (x : Fin (tags * card ^ dim)) :
    (elementEquiv card tags dim x).1.val = x.val / card ^ dim :=
  elementEquiv_tag_val_internal x

/-- Coordinates are the base-`card` digits of the tuple-block remainder. -/
theorem elementEquiv_coord_val {card : Nat} (x : Fin (tags * card ^ dim)) (j : Fin dim) :
    ((elementEquiv card tags dim x).2 j).val = tupleDigits card dim (x.val % card ^ dim) j :=
  elementEquiv_coord_val_internal x j

/-- Packing a tagged tuple adds its positional numeral to its tag block's offset. -/
theorem elementEquiv_symm_val {card : Nat} (tag : Fin tags) (coords : Fin dim → Fin card) :
    ((elementEquiv card tags dim).symm (tag, coords)).val =
      tupleIndex card (fun j => (coords j).val) + card ^ dim * tag.val :=
  elementEquiv_symm_val_internal tag coords

/-- The Boolean structure map represents the original interpretation exactly. -/
@[simp] theorem applyDec_toFinStruct (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) : (I.applyDec A).toFinStruct = I.apply A.toFinStruct :=
  applyDec_toFinStruct_internal I A

/-- Arithmetic relation generation writes the interpreted relation's exact truth table. -/
theorem relationTableCode_encodeStruct (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) (r : Fin W.numRels) :
    I.relationTableCode r A.card (encodeStruct A) = encodeRelC ((I.applyDec A).rel r) :=
  relationTableCode_encodeStruct_internal I A r

/-- Arithmetic constant generation recovers the exact packed distinguished element. -/
theorem constantCode_encodeStruct (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) (c : Fin W.numConsts) :
    I.constantCode c A.card (encodeStruct A) = ((I.applyDec A).const c).val :=
  constantCode_encodeStruct_internal I A c

/-- The arithmetic generator produces exactly the interpreted structure's binary encoding. -/
theorem rawEncoding_encodeStruct (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) : I.rawEncoding A.card (encodeStruct A) = encodeStruct (I.applyDec A) :=
  rawEncoding_encodeStruct_internal I A

/-- The full output includes all target relation tables and one-hot constant blocks. -/
@[simp] theorem rawEncoding_length (I : TaggedFOInterpretation V W tags dim)
    (card : Nat) (input : List Bool) :
    (I.rawEncoding card input).length = encodingLength W (tags * card ^ dim) :=
  rawEncoding_length_internal I card input

/-- A valid input maps to the encoding of its interpreted structure. -/
@[simp] theorem mapEncoding_encodeStruct (I : TaggedFOInterpretation V W tags dim)
    (A : DecFinStruct V) :
    I.mapEncoding (encodeStruct A) = encodeStruct (I.applyDec A) := by
  simp only [mapEncoding, decodeStruct_encodeStruct]

/-- Every malformed input maps to the fixed non-encoding `[]`. -/
theorem mapEncoding_of_decode_eq_none (I : TaggedFOInterpretation V W tags dim)
    (input : List Bool) (h : decodeStruct V input = none) : I.mapEncoding input = [] := by
  simp only [mapEncoding, h]

end Complexity.DescriptiveComplexity.TaggedFOInterpretation
