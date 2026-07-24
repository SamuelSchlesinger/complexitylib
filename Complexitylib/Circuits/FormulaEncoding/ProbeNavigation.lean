/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Defs
import Complexitylib.Circuits.FormulaEncoding.ProbeNavigation.Internal

/-!
# Probe-oriented navigation in canonical formula codes

This module replaces an in-memory formula bit list by a position-indexed bit
oracle. Explicit fuel makes every decoder total on malformed sources. On a
canonical encoded token stream, enough fuel recovers exactly the same tokens,
bit spans, subtree widths, and binary child segments as list-backed navigation.

## Main results

- `FormulaCode.BitOracle.tokenAt?_ofList_encodeTokenStream` gives exact token
  access and its half-open bit span.
- `FormulaCode.BitOracle.encodedSubtreeWidth?_ofList_encodeTokenStream` agrees
  with postfix token navigation.
- `FormulaCode.BitOracle.encodedBinaryChildren?_ofList_encodeTokenStream`
  recovers exact child segments in arbitrary token context.
-/

namespace Complexity

namespace FormulaCode

namespace BitOracle

/-- A terminated-unary natural can be decoded through position-indexed probes
at an arbitrary canonical field boundary. -/
theorem decodeNatAt?_ofList_append_encode
    (before after : List Bool) (value extraFuel accumulator : ℕ) :
    decodeNatAt?
        (ofList (before ++ CircuitCode.NatCode.encode value ++ after))
        (value + 1 + extraFuel) before.length accumulator =
      some (accumulator + value, before.length + value + 1) :=
  decodeNatAt?_ofList_append_encode_internal before after value extraFuel
    accumulator

/-- Probing a canonical token field recovers the token and advances by exactly
its encoded length. -/
theorem decodeTokenAt?_ofList_append_encode
    (before after : List Bool) (token : Token) (extraFuel : ℕ) :
    decodeTokenAt? (ofList (before ++ token.encode ++ after))
        (token.codeLength + extraFuel) before.length =
      some (token, before.length + token.codeLength) :=
  decodeTokenAt?_ofList_append_encode_internal before after token extraFuel

/-- The oracle decoder recovers the exact count and payload cursor of a
canonically framed token stream. -/
theorem tokenHeader?_ofList_encodeTokenStream
    (stream : List Token) (extraFuel : ℕ) :
    tokenHeader? (ofList (encodeTokenStream stream))
        (stream.length + 1 + extraFuel) =
      some ⟨stream.length, stream.length + 1⟩ :=
  tokenHeader?_ofList_encodeTokenStream_internal stream extraFuel

/-- With enough fuel for the header and every token field, a valid ordinal
returns its exact token and half-open bit span. -/
theorem tokenAt?_ofList_encodeTokenStream
    (stream : List Token) (bitFuel index : ℕ)
    (hheader : stream.length + 1 ≤ bitFuel)
    (hindex : index < stream.length)
    (hbound : ∀ token ∈ stream, token.codeLength ≤ bitFuel) :
    tokenAt? (ofList (encodeTokenStream stream)) bitFuel index =
      some
        ⟨stream[index], stream.length + 1 + tokenBitOffset stream index,
          stream.length + 1 + tokenBitOffset stream index +
            stream[index].codeLength⟩ :=
  tokenAt?_ofList_encodeTokenStream_internal stream bitFuel index hheader
    hindex hbound

/-- Oracle token access returns the canonical token at every valid ordinal. -/
theorem tokenValueAt?_ofList_encodeTokenStream
    (stream : List Token) (bitFuel index : ℕ)
    (hheader : stream.length + 1 ≤ bitFuel)
    (hindex : index < stream.length)
    (hbound : ∀ token ∈ stream, token.codeLength ≤ bitFuel) :
    tokenValueAt? (ofList (encodeTokenStream stream)) bitFuel index =
      some stream[index] :=
  tokenValueAt?_ofList_encodeTokenStream_internal stream bitFuel index hheader
    hindex hbound

/-- Oracle-driven backwards scanning agrees with token-list navigation on a
canonical framed stream. -/
theorem encodedSubtreeWidth?_ofList_encodeTokenStream
    (stream : List Token) (bitFuel root : ℕ)
    (hheader : stream.length + 1 ≤ bitFuel)
    (hroot : root < stream.length)
    (hbound : ∀ token ∈ stream, token.codeLength ≤ bitFuel) :
    encodedSubtreeWidth? (ofList (encodeTokenStream stream))
        bitFuel root = subtreeWidth? stream root :=
  encodedSubtreeWidth?_ofList_encodeTokenStream_internal stream bitFuel root
    hheader hroot hbound

/-- Oracle-driven scanning recovers a canonical subtree embedded between
arbitrary token prefixes and suffixes. -/
theorem encodedSubtreeWidth?_ofList_encodeTokenStream_context
    (before after : List Token) (formula : BoolFormula) (bitFuel : ℕ)
    (hheader : (before ++ tokens formula ++ after).length + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ before ++ tokens formula ++ after,
      token.codeLength ≤ bitFuel) :
    encodedSubtreeWidth?
        (ofList (encodeTokenStream (before ++ tokens formula ++ after)))
        bitFuel (before.length + formula.size - 1) =
      some formula.size :=
  encodedSubtreeWidth?_ofList_encodeTokenStream_context_internal before after
    formula bitFuel hheader hbound

/-- At a canonical binary postfix segment, oracle navigation recovers the
exact left and right child segments. -/
theorem encodedBinaryChildren?_ofList_encodeTokenStream
    (before after : List Token) (left right : BoolFormula)
    (op : Token) (bitFuel : ℕ)
    (hheader :
      (before ++ tokens left ++ tokens right ++ [op] ++ after).length + 1 ≤
        bitFuel)
    (hbound : ∀ token ∈
      before ++ tokens left ++ tokens right ++ [op] ++ after,
        token.codeLength ≤ bitFuel) :
    encodedBinaryChildren?
        (ofList (encodeTokenStream
          (before ++ tokens left ++ tokens right ++ [op] ++ after)))
        bitFuel ⟨before.length, left.size + right.size + 1⟩ =
      some (⟨before.length, left.size⟩,
        ⟨before.length + left.size, right.size⟩) :=
  encodedBinaryChildren?_ofList_encodeTokenStream_internal before after left
    right op bitFuel hheader hbound

end BitOracle

end FormulaCode

end Complexity
