/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Positions.Defs
public import Complexitylib.DescriptiveComplexity.Encoding.Positions.Internal

/-!
# Reading the structure encoding by table site

The computable positions recover every relation and constant-table bit. The
full encoded length is strictly increasing with universe size, so at a fixed
input length there can be at most one structure size.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Every relation and constant-table site occurs in the encoder's ordering. -/
theorem mem_encodingTableSites (V : Vocabulary) (card : Nat) (site : InputSite V card) :
    site ∈ encodingTableSites V card := mem_encodingTableSites_internal V card site

/-- Every table position lies within the full encoded input. -/
theorem encodingPosition_lt (V : Vocabulary) (card : Nat) (site : InputSite V card) :
    encodingPosition V card site < encodingLength V card :=
  encodingPosition_lt_internal V card site

/-- The existing structure encoder has the named encoded length. -/
theorem encodeStruct_length_eq {V : Vocabulary} (A : DecFinStruct V) :
    (encodeStruct A).length = encodingLength V A.card := encodeStruct_length A

/-- Reading a table site's computed position recovers exactly its stored value. -/
theorem getElem?_encodeStruct_position {V : Vocabulary} (A : DecFinStruct V)
    (site : InputSite V A.card) :
    (encodeStruct A)[encodingPosition V A.card site]? = some (inputSiteValue A site) :=
  getElem?_encodeStruct_position_internal A site

/-- The unary prefix alone is longer than the represented universe size. -/
theorem card_lt_encodingLength (V : Vocabulary) (card : Nat) :
    card < encodingLength V card := by
  unfold encodingLength
  omega

/-- Encoded lengths are positive even when all relation and constant tables are empty. -/
theorem encodingLength_pos (V : Vocabulary) (card : Nat) : 0 < encodingLength V card :=
  Nat.lt_of_le_of_lt (Nat.zero_le card) (card_lt_encodingLength V card)

instance (V : Vocabulary) (card : Nat) : NeZero (encodingLength V card) :=
  ⟨Nat.ne_of_gt (encodingLength_pos V card)⟩

/-- The unary prefix makes encoded length strictly increasing in universe size. -/
theorem encodingLength_strictMono (V : Vocabulary) : StrictMono (encodingLength V) :=
  encodingLength_strictMono_internal V

/-- Every table site occurs exactly once in the encoder's ordering. -/
theorem encodingTableSites_nodup (V : Vocabulary) (card : Nat) :
    (encodingTableSites V card).Nodup := encodingTableSites_nodup_internal V card

/-- The header contains `card` true bits followed by the false terminator. -/
theorem getElem?_encodeStruct_header {V : Vocabulary} (A : DecFinStruct V)
    (i : Fin (A.card + 1)) :
    (encodeStruct A)[i.val]? = some (decide (i.val < A.card)) :=
  getElem?_encodeStruct_header_internal A i

/-- Correct length, header, and table bits characterize the full encoding. -/
theorem encodeStruct_eq_of_values {V : Vocabulary} (A : DecFinStruct V)
    (bits : List Bool) (hlen : bits.length = encodingLength V A.card)
    (hheader : ∀ i : Fin (A.card + 1), bits[i.val]? = some (decide (i.val < A.card)))
    (hsites : ∀ site, bits[encodingPosition V A.card site]? = some (inputSiteValue A site)) :
    encodeStruct A = bits := encodeStruct_eq_of_values_internal A bits hlen hheader hsites

end Complexity.DescriptiveComplexity
