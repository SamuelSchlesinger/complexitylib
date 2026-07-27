/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding
public import Complexitylib.Circuits.FormulaEncoding.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Boolean-formula codec internals

This module proves the stack-machine, round-trip, injectivity, and length
properties of the canonical postfix formula encoding.
-/

@[expose] public section

namespace Complexity

namespace FormulaCode

namespace Token

/-- Internal exact length of one encoded token. -/
theorem length_encode_internal (token : Token) :
    token.encode.length = token.codeLength := by
  cases token <;>
    simp [encode, codeLength, CircuitCode.NatCode.length_encode]

/-- Internal token-prefix round trip. -/
theorem decodePrefix?_encode_append_internal
    (token : Token) (suffix : List Bool) :
    decodePrefix? (token.encode ++ suffix) = some (token, suffix) := by
  cases token <;>
    simp [encode, decodePrefix?]

end Token

/-- Internal composition law for the postfix stack machine. -/
theorem run?_append_internal
    (first second : List Token) (stack : List BoolFormula) :
    run? (first ++ second) stack =
      (run? first stack).bind (run? second) := by
  induction first generalizing stack with
  | nil => simp [run?]
  | cons token first ih =>
      simp only [List.cons_append, run?]
      cases happly : token.apply? stack with
      | none => simp
      | some next => simp [ih]

/-- Internal stack specification for the postfix tokens of a formula. -/
theorem run?_tokens_internal (formula : BoolFormula)
    (stack : List BoolFormula) :
    run? (tokens formula) stack = some (formula :: stack) := by
  induction formula generalizing stack with
  | var index => simp [tokens, run?, Token.apply?]
  | tru => simp [tokens, run?, Token.apply?]
  | fls => simp [tokens, run?, Token.apply?]
  | neg formula ih =>
      rw [tokens, run?_append_internal, ih]
      simp [run?, Token.apply?]
  | conj left right ihLeft ihRight =>
      rw [tokens, run?_append_internal,
        run?_append_internal, ihLeft]
      simp only [Option.bind_some]
      rw [ihRight]
      simp [run?, Token.apply?]
  | disj left right ihLeft ihRight =>
      rw [tokens, run?_append_internal,
        run?_append_internal, ihLeft]
      simp only [Option.bind_some]
      rw [ihRight]
      simp [run?, Token.apply?]

/-- Internal reconstruction of a formula from its own postfix tokens. -/
theorem build?_tokens_internal (formula : BoolFormula) :
    build? (tokens formula) = some formula := by
  simp [build?, run?_tokens_internal]

/-- Internal exact token-count theorem. -/
theorem length_tokens_internal (formula : BoolFormula) :
    (tokens formula).length = formula.size := by
  induction formula with
  | var index => simp [tokens, BoolFormula.size]
  | tru => simp [tokens, BoolFormula.size]
  | fls => simp [tokens, BoolFormula.size]
  | neg formula ih => simp [tokens, BoolFormula.size, ih]
  | conj left right ihLeft ihRight =>
      simp [tokens, BoolFormula.size, ihLeft, ihRight]
      omega
  | disj left right ihLeft ihRight =>
      simp [tokens, BoolFormula.size, ihLeft, ihRight]
      omega

/-- Internal fixed-count token-list round trip. -/
theorem decodeTokens?_flatMap_encode_append_internal
    (stream : List Token) (suffix : List Bool) :
    decodeTokens? stream.length (stream.flatMap Token.encode ++ suffix) =
      some (stream, suffix) := by
  induction stream with
  | nil => simp [decodeTokens?]
  | cons token stream ih =>
      simp [decodeTokens?, ih, List.append_assoc,
        Token.decodePrefix?_encode_append_internal]

/-- Internal formula-prefix round trip. -/
theorem decodePrefix?_encode_append_internal
    (formula : BoolFormula) (suffix : List Bool) :
    decodePrefix? (encode formula ++ suffix) = some (formula, suffix) := by
  simp [decodePrefix?, encode, List.append_assoc,
    decodeTokens?_flatMap_encode_append_internal, build?_tokens_internal]

/-- Internal exact-decoder round trip. -/
theorem decode?_encode_internal (formula : BoolFormula) :
    decode? (encode formula) = some formula := by
  unfold decode?
  rw [show encode formula = encode formula ++ [] by simp,
    decodePrefix?_encode_append_internal]

/-- Internal injectivity of canonical formula serialization. -/
theorem encode_injective_internal : Function.Injective encode := by
  intro left right heq
  have hleft := decode?_encode_internal left
  have hright := decode?_encode_internal right
  rw [heq] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

/-- Internal rejection of nonempty trailing data by exact decoding. -/
theorem decode?_encode_append_eq_none_internal
    (formula : BoolFormula) {suffix : List Bool} (hsuffix : suffix ≠ []) :
    decode? (encode formula ++ suffix) = none := by
  unfold decode?
  rw [decodePrefix?_encode_append_internal]
  simp [hsuffix]

/-- Internal exact formula-code length. -/
theorem length_encode_internal (formula : BoolFormula) :
    (encode formula).length =
      formula.size + 1 +
        ((tokens formula).map Token.codeLength).sum := by
  simp [encode, CircuitCode.NatCode.length_encode, List.length_flatMap,
    Token.length_encode_internal, length_tokens_internal]

end FormulaCode

end Complexity
