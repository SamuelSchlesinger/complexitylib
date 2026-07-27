/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Defs
public import Complexitylib.Circuits.Formula

/-!
# Machine-facing encoding of Boolean formulas

This file defines a canonical postfix encoding of `BoolFormula`. Six three-bit
tags represent variables, constants, and connectives. A variable tag is
followed by the existing terminated-unary natural code. The complete stream
starts with its terminated-unary token count.

Postfix order makes decoding iterative: the parser first reads a flat token
stream, then a stack machine reconstructs the formula. This avoids a recursive
on-tape tree parser and gives the later Barrington generator a simple,
self-delimiting input language.
-/

@[expose] public section

namespace Complexity

namespace FormulaCode

/-- Proof-free postfix tokens for Boolean formulas. -/
inductive Token where
  /-- A variable with its natural-number index. -/
  | var (index : ℕ)
  /-- The constant true. -/
  | tru
  /-- The constant false. -/
  | fls
  /-- Unary negation. -/
  | neg
  /-- Binary conjunction. -/
  | conj
  /-- Binary disjunction. -/
  | disj
  deriving DecidableEq, Repr

namespace Token

/-- Serialize one postfix token. Tags `110` and `111` are reserved. -/
def encode : Token → List Bool
  | .var index => [false, false, false] ++ CircuitCode.NatCode.encode index
  | .tru => [false, false, true]
  | .fls => [false, true, false]
  | .neg => [false, true, true]
  | .conj => [true, false, false]
  | .disj => [true, false, true]

/-- Parse one token prefix and return the unused suffix. -/
def decodePrefix? : List Bool → Option (Token × List Bool)
  | false :: false :: false :: rest => do
      let (index, rest) ← CircuitCode.NatCode.decodePrefix? rest
      some (.var index, rest)
  | false :: false :: true :: rest => some (.tru, rest)
  | false :: true :: false :: rest => some (.fls, rest)
  | false :: true :: true :: rest => some (.neg, rest)
  | true :: false :: false :: rest => some (.conj, rest)
  | true :: false :: true :: rest => some (.disj, rest)
  | _ => none

/-- The exact number of bits in a token encoding. -/
def codeLength : Token → ℕ
  | .var index => index + 4
  | _ => 3

/-- Apply one postfix token to a formula stack. -/
def apply? : Token → List BoolFormula → Option (List BoolFormula)
  | .var index, stack => some (.var index :: stack)
  | .tru, stack => some (.tru :: stack)
  | .fls, stack => some (.fls :: stack)
  | .neg, formula :: stack => some (.neg formula :: stack)
  | .conj, right :: left :: stack => some (.conj left right :: stack)
  | .disj, right :: left :: stack => some (.disj left right :: stack)
  | _, _ => none

end Token

/-- Canonical postfix tokens of a formula. -/
def tokens : BoolFormula → List Token
  | .var index => [.var index]
  | .tru => [.tru]
  | .fls => [.fls]
  | .neg formula => tokens formula ++ [.neg]
  | .conj left right => tokens left ++ tokens right ++ [.conj]
  | .disj left right => tokens left ++ tokens right ++ [.disj]

/-- Execute a postfix token stream from an initial formula stack. -/
def run? : List Token → List BoolFormula → Option (List BoolFormula)
  | [], stack => some stack
  | token :: tokens, stack => do
      let stack ← token.apply? stack
      run? tokens stack

/-- Reconstruct exactly one formula from a postfix token stream. -/
def build? (stream : List Token) : Option BoolFormula := do
  let stack ← run? stream []
  match stack with
  | [formula] => some formula
  | _ => none

/-- Decode exactly `count` token prefixes and return the unused bit suffix. -/
def decodeTokens? : ℕ → List Bool → Option (List Token × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (token, rest) ← Token.decodePrefix? bits
      let (stream, rest) ← decodeTokens? count rest
      some (token :: stream, rest)

/-- Canonically encode a Boolean formula. -/
def encode (formula : BoolFormula) : List Bool :=
  CircuitCode.NatCode.encode (tokens formula).length ++
    (tokens formula).flatMap Token.encode

/-- Decode one complete formula prefix and return the unused suffix. -/
def decodePrefix? (bits : List Bool) : Option (BoolFormula × List Bool) := do
  let (count, rest) ← CircuitCode.NatCode.decodePrefix? bits
  let (stream, rest) ← decodeTokens? count rest
  let formula ← build? stream
  some (formula, rest)

/-- Decode exactly one formula. Trailing bits are rejected. -/
def decode? (bits : List Bool) : Option BoolFormula :=
  match decodePrefix? bits with
  | some (formula, []) => some formula
  | _ => none

end FormulaCode

end Complexity
