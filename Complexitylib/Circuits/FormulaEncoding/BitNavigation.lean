/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Defs
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Internal

/-!
# Bit-level navigation in canonical formula codes

This module gives the uniform Barrington controller an exact sequential-cursor
view of canonical formula bits. A token ordinal determines its token and exact
half-open bit span without reconstructing an inductive formula.

## Main results

- `FormulaCode.Token.decodeAt?_append_encode` -- exact absolute token cursor.
- `FormulaCode.tokenAt?_encodeTokenStream` -- exact access in framed streams.
- `FormulaCode.tokenHeader?_encode` -- exact count and payload cursor.
- `FormulaCode.tokenAt?_encode` -- exact token and bit span by ordinal.
- `FormulaCode.encodedSubtreeWidth?_encode` -- encoded and token scans agree.
- `FormulaCode.encodedBinaryChildren?_encodeTokenStream` -- exact child spans.
-/

namespace Complexity

namespace FormulaCode

/-- Extending a valid token prefix by one advances its encoded-bit length by
exactly the selected token's code length. -/
theorem tokensCodeLength_take_succ (stream : List Token)
    (index : ℕ) (hindex : index < stream.length) :
    tokensCodeLength (stream.take (index + 1)) =
      tokensCodeLength (stream.take index) + stream[index].codeLength :=
  tokensCodeLength_take_succ_internal stream index hindex

namespace Token

/-- Decoding at the boundary after `prefix` recovers the token and advances
by exactly its declared encoded length. -/
theorem decodeAt?_append_encode (beforeBits : List Bool)
    (token : Token) (suffix : List Bool) :
    decodeAt? (beforeBits ++ token.encode ++ suffix) beforeBits.length =
      some (token, beforeBits.length + token.codeLength) :=
  decodeAt?_append_encode_internal beforeBits token suffix

end Token

/-- Locating a valid ordinal in any canonically framed token stream returns
the exact token and half-open bit span. -/
theorem tokenAt?_encodeTokenStream (stream : List Token)
    (index : ℕ) (hindex : index < stream.length) :
    tokenAt? (encodeTokenStream stream) index =
      some
        ⟨stream[index], stream.length + 1 + tokenBitOffset stream index,
          stream.length + 1 + tokenBitOffset stream index +
            stream[index].codeLength⟩ :=
  tokenAt?_encodeTokenStream_internal stream index hindex

/-- The encoded token count is followed immediately by the token payload. -/
theorem tokenHeader?_encode (formula : BoolFormula) :
    tokenHeader? (encode formula) =
      some ⟨formula.size, formula.size + 1⟩ :=
  tokenHeader?_encode_internal formula

/-- Locating a valid token ordinal in a canonical formula code returns the
exact postfix token and its exact half-open bit span. -/
theorem tokenAt?_encode (formula : BoolFormula)
    (index : ℕ) (hindex : index < (tokens formula).length) :
    tokenAt? (encode formula) index =
      some
        ⟨(tokens formula)[index], formula.size + 1 +
            tokenBitOffset (tokens formula) index,
          formula.size + 1 + tokenBitOffset (tokens formula) index +
            ((tokens formula)[index]).codeLength⟩ :=
  tokenAt?_encode_internal formula index hindex

/-- Token-only access to a valid canonical ordinal returns its exact postfix
token. -/
theorem tokenValueAt?_encode (formula : BoolFormula)
    (index : ℕ) (hindex : index < (tokens formula).length) :
    tokenValueAt? (encode formula) index = some (tokens formula)[index] :=
  tokenValueAt?_encode_internal formula index hindex

/-- Token-only access agrees with indexing any canonically framed token
stream. -/
theorem tokenValueAt?_encodeTokenStream (stream : List Token)
    (index : ℕ) (hindex : index < stream.length) :
    tokenValueAt? (encodeTokenStream stream) index = some stream[index] :=
  tokenValueAt?_encodeTokenStream_internal stream index hindex

/-- Query-driven subtree scanning agrees with token-list navigation for any
canonically framed token stream. -/
theorem encodedSubtreeWidth?_encodeTokenStream
    (stream : List Token) (root : ℕ) (hroot : root < stream.length) :
    encodedSubtreeWidth? (encodeTokenStream stream) root =
      subtreeWidth? stream root :=
  encodedSubtreeWidth?_encodeTokenStream_internal stream root hroot

/-- Query-driven scanning recovers a canonical subtree embedded between
arbitrary token prefixes and suffixes. -/
theorem encodedSubtreeWidth?_encodeTokenStream_context
    (before after : List Token) (formula : BoolFormula) :
    encodedSubtreeWidth?
        (encodeTokenStream (before ++ tokens formula ++ after))
        (before.length + formula.size - 1) = some formula.size :=
  encodedSubtreeWidth?_encodeTokenStream_context_internal before after formula

/-- Splitting a canonical binary postfix segment inside an arbitrary framed
token stream recovers the exact left and right child segments. -/
theorem encodedBinaryChildren?_encodeTokenStream
    (before after : List Token) (left right : BoolFormula)
    (op : Token) :
    encodedBinaryChildren?
        (encodeTokenStream
          (before ++ tokens left ++ tokens right ++ [op] ++ after))
        ⟨before.length, left.size + right.size + 1⟩ =
      some (⟨before.length, left.size⟩,
        ⟨before.length + left.size, right.size⟩) :=
  encodedBinaryChildren?_encodeTokenStream_internal before after left right op

/-- The owed-subtree scan implemented by repeated encoded-token queries agrees
with navigation on the canonical postfix token stream. -/
theorem encodedSubtreeWidth?_encode (formula : BoolFormula)
    (root : ℕ) (hroot : root < (tokens formula).length) :
    encodedSubtreeWidth? (encode formula) root =
      subtreeWidth? (tokens formula) root :=
  encodedSubtreeWidth?_encode_internal formula root hroot

/-- Encoded scanning recovers the same subtree start as token-stream
navigation. -/
theorem encodedSubtreeStart?_encode (formula : BoolFormula)
    (root : ℕ) (hroot : root < (tokens formula).length) :
    encodedSubtreeStart? (encode formula) root =
      subtreeStart? (tokens formula) root :=
  encodedSubtreeStart?_encode_internal formula root hroot

/-- The complete canonical encoded formula is one postfix subtree. -/
theorem encodedSubtreeWidth?_encode_root (formula : BoolFormula) :
    encodedSubtreeWidth? (encode formula) (formula.size - 1) =
      some formula.size :=
  encodedSubtreeWidth?_encode_root_internal formula

/-- At a canonical encoded conjunction, the right child occupies its exact
postfix token width immediately before the root. -/
theorem encodedSubtreeWidth?_encode_conj_right
    (left right : BoolFormula) :
    encodedSubtreeWidth? (encode (.conj left right))
      (left.size + right.size - 1) = some right.size :=
  encodedSubtreeWidth?_encode_conj_right_internal left right

/-- At a canonical encoded disjunction, the right child occupies its exact
postfix token width immediately before the root. -/
theorem encodedSubtreeWidth?_encode_disj_right
    (left right : BoolFormula) :
    encodedSubtreeWidth? (encode (.disj left right))
      (left.size + right.size - 1) = some right.size :=
  encodedSubtreeWidth?_encode_disj_right_internal left right

end FormulaCode

end Complexity
