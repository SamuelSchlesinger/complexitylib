/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.Navigation.Defs

/-!
# Bit-level navigation in canonical formula codes -- definitions

The uniform Barrington controller receives formula bits from a restartable
transducer rather than an in-memory token list. These definitions expose the
sequential cursor semantics needed by that controller: decode one token at a
bit position, seek to a token ordinal, and retain the exact half-open bit span
of the selected token.
-/

namespace Complexity

namespace FormulaCode

/-- A decoded token together with its half-open interval in the complete
formula code. -/
structure LocatedToken where
  /-- The decoded postfix token. -/
  token : Token
  /-- Bit position of the token's first tag bit. -/
  startBit : ℕ
  /-- First bit position after the complete token encoding. -/
  nextBit : ℕ
  deriving DecidableEq

/-- The decoded token count and the first bit position of the token payload. -/
structure TokenHeader where
  /-- Number of postfix tokens declared by the terminated-unary header. -/
  count : ℕ
  /-- First bit position following the header. -/
  payloadStart : ℕ
  deriving DecidableEq

/-- A half-open interval of token ordinals in one framed postfix stream. -/
structure TokenSegment where
  /-- First token ordinal in the segment. -/
  start : ℕ
  /-- Number of tokens in the segment. -/
  width : ℕ
  deriving DecidableEq

namespace TokenSegment

/-- Root ordinal of a nonempty postfix segment. -/
def root? : TokenSegment → Option ℕ
  | ⟨_, 0⟩ => none
  | ⟨start, width + 1⟩ => some (start + width)

/-- Remove the final root token from a nonempty postfix segment. -/
def dropRoot? : TokenSegment → Option TokenSegment
  | ⟨_, 0⟩ => none
  | ⟨start, width + 1⟩ => some ⟨start, width⟩

end TokenSegment

namespace Token

/-- Decode one token starting at an absolute bit cursor. The returned cursor
is the first bit after that token. -/
def decodeAt? (bits : List Bool) (cursor : ℕ) : Option (Token × ℕ) := do
  let (token, rest) ← decodePrefix? (bits.drop cursor)
  some (token, bits.length - rest.length)

end Token

/-- Total encoded length of a postfix token stream, excluding the formula
header. -/
def tokensCodeLength (stream : List Token) : ℕ :=
  (stream.map Token.codeLength).sum

/-- Encoded payload offset of token ordinal `index`. For an out-of-range
ordinal this is the length of the complete available prefix. -/
def tokenBitOffset (stream : List Token) (index : ℕ) : ℕ :=
  tokensCodeLength (stream.take index)

/-- Frame an arbitrary postfix token stream with its terminated-unary token
count. Canonical formula codes are this construction applied to `tokens`. -/
def encodeTokenStream (stream : List Token) : List Bool :=
  CircuitCode.NatCode.encode stream.length ++
    stream.flatMap Token.encode

/-- Decode the formula token-count header and retain the absolute payload
cursor. -/
def tokenHeader? (bits : List Bool) : Option TokenHeader := do
  let (count, rest) ← CircuitCode.NatCode.decodePrefix? bits
  some ⟨count, bits.length - rest.length⟩

/-- Seek forward from an already-known token boundary and locate the token at
the supplied relative ordinal. -/
def seekToken? (bits : List Bool) (cursor : ℕ) : ℕ → Option LocatedToken
  | 0 => do
      let (token, nextBit) ← Token.decodeAt? bits cursor
      some ⟨token, cursor, nextBit⟩
  | index + 1 => do
      let (_, nextBit) ← Token.decodeAt? bits cursor
      seekToken? bits nextBit index

/-- Locate one declared token ordinal in a complete encoded formula. Malformed
headers, malformed token prefixes, and out-of-range ordinals fail. -/
def tokenAt? (bits : List Bool) (index : ℕ) : Option LocatedToken := do
  let header ← tokenHeader? bits
  if index < header.count then
    seekToken? bits header.payloadStart index
  else
    none

/-- Forget the bit span and query only the decoded token value. -/
def tokenValueAt? (bits : List Bool) (index : ℕ) : Option Token :=
  (tokenAt? bits index).map LocatedToken.token

/-- Predecessor of a token ordinal, with `none` before ordinal zero. -/
def previousToken? : ℕ → Option ℕ
  | 0 => none
  | cursor + 1 => some cursor

/-- Run the owed-subtree scan through a random-access token query. `fuel`
bounds the number of inspected ordinals, while `cursor` moves strictly
backwards. -/
def backwardScanQuery? (query : ℕ → Option Token) :
    ℕ → Option ℕ → ℕ → Option ℕ
  | _, _, 0 => some 0
  | 0, _, _ + 1 => none
  | _ + 1, none, _ + 1 => none
  | fuel + 1, some cursor, owed + 1 => do
      let token ← query cursor
      let consumed ← backwardScanQuery? query fuel
        (previousToken? cursor) (owed + token.arity)
      some (consumed + 1)

/-- Width in tokens of the postfix subtree ending at `root`, obtained solely
through repeated token-ordinal queries on encoded bits. -/
def encodedSubtreeWidth? (bits : List Bool) (root : ℕ) : Option ℕ :=
  backwardScanQuery? (tokenValueAt? bits) (root + 1) (some root) 1

/-- Start token ordinal of the encoded postfix subtree ending at `root`. -/
def encodedSubtreeStart? (bits : List Bool) (root : ℕ) : Option ℕ := do
  let width ← encodedSubtreeWidth? bits root
  if width ≤ root + 1 then some (root + 1 - width) else none

/-- Split a postfix segment below a binary root. The right-child width is
recovered by the query-driven backwards scan; both children must be nonempty
and contained in the rootless body. -/
def encodedBinaryChildren? (bits : List Bool)
    (segment : TokenSegment) : Option (TokenSegment × TokenSegment) := do
  let root ← segment.root?
  let body ← segment.dropRoot?
  let rightRoot ← previousToken? root
  let rightWidth ← encodedSubtreeWidth? bits rightRoot
  if 0 < rightWidth ∧ rightWidth < body.width then
    let leftWidth := body.width - rightWidth
    some (⟨body.start, leftWidth⟩,
      ⟨body.start + leftWidth, rightWidth⟩)
  else
    none

end FormulaCode

end Complexity
