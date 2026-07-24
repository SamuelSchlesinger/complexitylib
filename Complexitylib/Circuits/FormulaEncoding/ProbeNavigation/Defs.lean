/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding.BitNavigation.Defs

/-!
# Probe-oriented navigation in formula codes -- definitions

An `OutputProbe` invocation exposes one source-output bit at a numeric position;
it does not expose the complete output list. This layer expresses formula-code
navigation against exactly that oracle. The explicit bit fuel makes malformed
or unterminated fields total, while canonical fields succeed once the fuel
covers the inspected prefix.
-/

namespace Complexity

namespace FormulaCode

/-- A random-access bit source. `none` denotes an unavailable position. -/
abbrev BitOracle := ℕ → Option Bool

namespace BitOracle

/-- The random-access oracle backed by an in-memory bit list. -/
def ofList (bits : List Bool) : BitOracle := fun index => bits[index]?

/-- Scan one terminated-unary natural field. The cursor returned on success is
the first position following the zero terminator. -/
def decodeNatAt? (query : BitOracle) : ℕ → ℕ → ℕ →
    Option (ℕ × ℕ)
  | 0, _, _ => none
  | fuel + 1, cursor, value => do
      let bit ← query cursor
      if bit then
        decodeNatAt? query fuel (cursor + 1) (value + 1)
      else
        some (value, cursor + 1)

/-- Decode one postfix token by probing its three tag positions and, for a
variable, its following terminated-unary index. -/
def decodeTokenAt? (query : BitOracle) (bitFuel cursor : ℕ) :
    Option (Token × ℕ) := do
  let tag₀ ← query cursor
  let tag₁ ← query (cursor + 1)
  let tag₂ ← query (cursor + 2)
  match tag₀, tag₁, tag₂ with
  | false, false, false =>
      let (index, nextBit) ←
        decodeNatAt? query bitFuel (cursor + 3) 0
      some (.var index, nextBit)
  | false, false, true => some (.tru, cursor + 3)
  | false, true, false => some (.fls, cursor + 3)
  | false, true, true => some (.neg, cursor + 3)
  | true, false, false => some (.conj, cursor + 3)
  | true, false, true => some (.disj, cursor + 3)
  | true, true, _ => none

/-- Decode the terminated-unary token count at the beginning of a formula
code. -/
def tokenHeader? (query : BitOracle) (bitFuel : ℕ) :
    Option TokenHeader := do
  let (count, payloadStart) ← decodeNatAt? query bitFuel 0 0
  some ⟨count, payloadStart⟩

/-- Seek from a known token boundary to a relative postfix-token ordinal. -/
def seekToken? (query : BitOracle) (bitFuel cursor : ℕ) :
    ℕ → Option LocatedToken
  | 0 => do
      let (token, nextBit) ← decodeTokenAt? query bitFuel cursor
      some ⟨token, cursor, nextBit⟩
  | index + 1 => do
      let (_, nextBit) ← decodeTokenAt? query bitFuel cursor
      seekToken? query bitFuel nextBit index

/-- Locate one declared postfix-token ordinal using only position-indexed bit
queries. -/
def tokenAt? (query : BitOracle) (bitFuel index : ℕ) :
    Option LocatedToken := do
  let header ← tokenHeader? query bitFuel
  if index < header.count then
    seekToken? query bitFuel header.payloadStart index
  else
    none

/-- Query only the token value at one declared ordinal. -/
def tokenValueAt? (query : BitOracle) (bitFuel index : ℕ) : Option Token :=
  (tokenAt? query bitFuel index).map LocatedToken.token

/-- Width of the postfix subtree rooted at `root`, using only oracle token
queries. -/
def encodedSubtreeWidth? (query : BitOracle) (bitFuel root : ℕ) :
    Option ℕ :=
  backwardScanQuery? (tokenValueAt? query bitFuel)
    (root + 1) (some root) 1

/-- Split a binary postfix segment using only oracle token queries. -/
def encodedBinaryChildren? (query : BitOracle) (bitFuel : ℕ)
    (segment : TokenSegment) : Option (TokenSegment × TokenSegment) := do
  let root ← segment.root?
  let body ← segment.dropRoot?
  let rightRoot ← previousToken? root
  let rightWidth ← encodedSubtreeWidth? query bitFuel rightRoot
  if 0 < rightWidth ∧ rightWidth < body.width then
    let leftWidth := body.width - rightWidth
    some (⟨body.start, leftWidth⟩,
      ⟨body.start + leftWidth, rightWidth⟩)
  else
    none

end BitOracle

end FormulaCode

end Complexity
