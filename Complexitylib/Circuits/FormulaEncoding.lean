/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.FormulaEncoding.Defs
public import Complexitylib.Circuits.FormulaEncoding.Internal

/-!
# Canonical postfix encoding of Boolean formulas

This module exposes the machine-facing input format for the uniform Barrington
generator. Formula nodes become a postfix stream of six three-bit token kinds;
variable tokens carry a terminated-unary index, and a terminated-unary token
count frames the complete stream.

The stack decoder is iterative, exact decoding is a left inverse, canonical
serialization is injective, and the code-length equation records every bit.

## Main results

- `FormulaCode.run?_tokens` -- postfix execution reconstructs a formula on any
  stack.
- `FormulaCode.decode?_encode` -- whole-formula round trip.
- `FormulaCode.encode_injective` -- canonical codes are unambiguous.
- `FormulaCode.length_encode` -- exact serialized length.
-/

@[expose] public section

namespace Complexity

namespace FormulaCode

namespace Token

/-- The declared token cost is its exact encoded length. -/
@[simp] theorem length_encode (token : Token) :
    token.encode.length = token.codeLength :=
  length_encode_internal token

/-- Decoding an encoded token in front of any suffix recovers both. -/
@[simp] theorem decodePrefix?_encode_append
    (token : Token) (suffix : List Bool) :
    decodePrefix? (token.encode ++ suffix) = some (token, suffix) :=
  decodePrefix?_encode_append_internal token suffix

end Token

/-- Running concatenated token streams is sequential stack execution. -/
theorem run?_append (first second : List Token)
    (stack : List BoolFormula) :
    run? (first ++ second) stack =
      (run? first stack).bind (run? second) :=
  run?_append_internal first second stack

/-- Running a formula's postfix tokens pushes exactly that formula. -/
@[simp] theorem run?_tokens (formula : BoolFormula)
    (stack : List BoolFormula) :
    run? (tokens formula) stack = some (formula :: stack) :=
  run?_tokens_internal formula stack

/-- Building from a formula's postfix stream recovers the formula. -/
@[simp] theorem build?_tokens (formula : BoolFormula) :
    build? (tokens formula) = some formula :=
  build?_tokens_internal formula

/-- The postfix stream has one token per formula node. -/
@[simp] theorem length_tokens (formula : BoolFormula) :
    (tokens formula).length = formula.size :=
  length_tokens_internal formula

/-- Fixed-count token decoding consumes exactly the supplied encoded stream. -/
@[simp] theorem decodeTokens?_flatMap_encode_append
    (stream : List Token) (suffix : List Bool) :
    decodeTokens? stream.length (stream.flatMap Token.encode ++ suffix) =
      some (stream, suffix) :=
  decodeTokens?_flatMap_encode_append_internal stream suffix

/-- Prefix decoding preserves a caller-supplied suffix. -/
@[simp] theorem decodePrefix?_encode_append
    (formula : BoolFormula) (suffix : List Bool) :
    decodePrefix? (encode formula ++ suffix) = some (formula, suffix) :=
  decodePrefix?_encode_append_internal formula suffix

/-- Exact decoding is a left inverse of canonical serialization. -/
@[simp] theorem decode?_encode (formula : BoolFormula) :
    decode? (encode formula) = some formula :=
  decode?_encode_internal formula

/-- Canonical formula serialization is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact decoding rejects nonempty trailing data. -/
theorem decode?_encode_append_eq_none
    (formula : BoolFormula) {suffix : List Bool} (hsuffix : suffix ≠ []) :
    decode? (encode formula ++ suffix) = none :=
  decode?_encode_append_eq_none_internal formula hsuffix

/-- Exact formula-code length: one framed token count followed by every token. -/
@[simp] theorem length_encode (formula : BoolFormula) :
    (encode formula).length =
      formula.size + 1 +
        ((tokens formula).map Token.codeLength).sum :=
  length_encode_internal formula

end FormulaCode

end Complexity
