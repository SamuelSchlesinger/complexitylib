/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.Basic

/-!
# Explicit binary codes for finite alphabets

An enumeration assigns index `i` to the palindromic codeword `false, true^i,
false`. Concatenation encodes words, including the empty word. Decoding rejects
missing delimiters and indices outside the enumeration. Reversing an encoding
therefore reverses its letters without changing their codes.
-/

@[expose] public section

namespace Complexity

/-- An explicit enumeration of an alphabet, including an empty alphabet. -/
structure FiniteAlphabetCode (α : Type) where
  /-- Number of letters. -/
  size : ℕ
  /-- Chosen numbering of the letters. -/
  index : α ≃ Fin size

namespace FiniteAlphabetCode

/-- Choose a code from a finite-alphabet instance. -/
noncomputable def ofFintype (α : Type) [Fintype α] : FiniteAlphabetCode α :=
  ⟨Fintype.card α, Fintype.equivFin α⟩

/-- A delimited unary symbol code, identical to its reversal. -/
def symbol {α : Type} (c : FiniteAlphabetCode α) (a : α) : List Bool :=
  false :: List.replicate (c.index a).val true ++ [false]

/-- Concatenate the symbol codes of a word. -/
def encode {α : Type} (c : FiniteAlphabetCode α) (w : List α) : List Bool :=
  w.flatMap c.symbol

/-- Decode a suffix while waiting for an opening delimiter or counting an open codeword. -/
def decodeFrom {α : Type} (c : FiniteAlphabetCode α) : Option ℕ → List Bool → Option (List α)
  | none, [] => some []
  | some _, [] => none
  | none, false :: bs => c.decodeFrom (some 0) bs
  | none, true :: _ => none
  | some i, true :: bs =>
      if i + 1 < c.size then c.decodeFrom (some (i + 1)) bs else none
  | some i, false :: bs =>
      if h : i < c.size then
        (c.decodeFrom none bs).map (c.index.symm ⟨i, h⟩ :: ·)
      else none

/-- Decode an entire word, rejecting every malformed code. -/
def decode {α : Type} (c : FiniteAlphabetCode α) (bits : List Bool) : Option (List α) :=
  c.decodeFrom none bits

/-- Encode a function's result on valid inputs and return empty output on invalid codes. -/
def map {α β : Type} (input : FiniteAlphabetCode α) (output : FiniteAlphabetCode β)
    (f : List α → List β) (bits : List Bool) : List Bool :=
  match input.decode bits with
  | none => []
  | some w => output.encode (f w)

end FiniteAlphabetCode
end Complexity
