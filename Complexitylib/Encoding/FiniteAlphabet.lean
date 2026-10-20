/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Encoding.FiniteAlphabet.Defs
import Complexitylib.Encoding.FiniteAlphabet.Internal

/-!
# Exact binary coding of finite alphabets

An explicit enumeration gives a delimited, palindromic unary code for each
letter. Encodings are injective, have linear length bounds, commute with word
reversal, and are exactly the strings accepted by the partial decoder. Empty
alphabets are supported, and only the empty word then has a valid encoding.
-/

public section

namespace Complexity.FiniteAlphabetCode

variable {α β : Type} (c : FiniteAlphabetCode α)

/-- Every encoded word is decoded exactly. -/
@[simp] theorem decode_encode (w : List α) : c.decode (c.encode w) = some w :=
  decode_encode_proof c w

/-- The decoder accepts precisely the chosen encodings. -/
theorem decode_eq_some_iff {bits : List Bool} {w : List α} :
    c.decode bits = some w ↔ c.encode w = bits := by
  constructor
  · exact encode_decode_proof c
  · rintro rfl
    exact c.decode_encode w

/-- Encoding distinct words gives distinct binary strings. -/
theorem encode_injective : Function.Injective c.encode := by
  intro xs ys h
  have he := congrArg c.decode h
  simpa only [decode_encode, Option.some.injEq] using he

/-- Encoded size is at least the source word length. -/
theorem length_le_encode (w : List α) : w.length ≤ (c.encode w).length :=
  encode_length_lower c w

/-- The alphabet enumeration determines a constant linear size bound. -/
theorem length_encode_le (w : List α) :
    (c.encode w).length ≤ (c.size + 1) * w.length :=
  encode_length_upper c w

/-- Palindromic symbol codes commute with reversal of the whole word. -/
theorem encode_reverse_eq (w : List α) : c.encode w.reverse = (c.encode w).reverse :=
  encode_reverse c w

/-- Reversal preserves validity and reverses the decoded letters. -/
theorem decode_reverse_eq (bits : List Bool) :
    c.decode bits.reverse = (c.decode bits).map List.reverse :=
  decode_reverse c bits

/-- A coded function has exactly its specified output on every encoded input. -/
@[simp] theorem map_encode (output : FiniteAlphabetCode β) (f : List α → List β) (w : List α) :
    c.map output f (c.encode w) = output.encode (f w) := by
  simp [map]

/-- A coded function returns empty output on every invalid code. -/
theorem map_invalid (output : FiniteAlphabetCode β) (f : List α → List β)
    {bits : List Bool} (h : c.decode bits = none) : c.map output f bits = [] := by
  simp [map, h]

end Complexity.FiniteAlphabetCode
