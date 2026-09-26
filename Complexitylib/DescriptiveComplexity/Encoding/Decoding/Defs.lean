/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Positions

/-!
# Decoding finite structures

Read a candidate structure using the encoder's exact bit positions, choosing the
first set bit in each constant block. The decoder checks the universe size and
encoded length, then accepts only if re-encoding the candidate reproduces the
whole input. This final check rejects malformed constant blocks, missing bits,
and trailing data. No machine running-time bound is asserted here.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Read a candidate; defaults make the operation total even on malformed input. -/
def readStructCandidate (V : Vocabulary) (card : Nat) (hcard : 2 ≤ card)
    (bits : List Bool) : DecFinStruct V where
  card := card
  hcard := hcard
  rel i args := bits[encodingPosition V card (.inl ⟨i, args⟩)]?.getD false
  const c := ((List.finRange card).find? (fun a =>
    bits[encodingPosition V card (.inr (c, a))]?.getD false)).getD ⟨0, by omega⟩

/-- Parse exactly the image of `encodeStruct`, returning `none` on malformed input. -/
def decodeStruct (V : Vocabulary) (bits : List Bool) : Option (DecFinStruct V) :=
  let card := (bits.takeWhile id).length
  if hcard : 2 ≤ card then
    if bits.length = encodingLength V card then
      let candidate := readStructCandidate V card hcard bits
      if encodeStruct candidate = bits then some candidate else none
    else none
  else none

end Complexity.DescriptiveComplexity
