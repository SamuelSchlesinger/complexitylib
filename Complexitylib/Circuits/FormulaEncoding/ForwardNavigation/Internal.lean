/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.FormulaEncoding
import Complexitylib.Circuits.FormulaEncoding.ForwardNavigation.Defs

/-!
# Forward navigation in postfix formula codes -- internals
-/

namespace Complexity

namespace FormulaCode

theorem forwardScan_append_internal
    (first second : List Token) (state : ForwardScanState) :
    forwardScan (first ++ second) state =
      forwardScan second (forwardScan first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons token first ih =>
      simp only [List.cons_append, forwardScan]
      exact ih (state.step token)

theorem forwardScan_take_succ_internal (stream : List Token)
    (state : ForwardScanState) (index : ℕ)
    (hindex : index < stream.length) :
    forwardScan (stream.take (index + 1)) state =
      (forwardScan (stream.take index) state).step stream[index] := by
  rw [← List.take_concat_get' stream index hindex,
    forwardScan_append_internal]
  rfl

theorem forwardScan_tokens_internal
    (formula : BoolFormula) (state : ForwardScanState) :
    forwardScan (tokens formula) state = state.afterFormula formula := by
  induction formula generalizing state with
  | var index =>
      simp [tokens, forwardScan, ForwardScanState.step,
        ForwardScanState.afterFormula, tokensCodeLength, Token.arity,
        Token.codeLength, BoolFormula.size]
  | tru =>
      simp [tokens, forwardScan, ForwardScanState.step,
        ForwardScanState.afterFormula, tokensCodeLength, Token.arity,
        Token.codeLength, BoolFormula.size]
  | fls =>
      simp [tokens, forwardScan, ForwardScanState.step,
        ForwardScanState.afterFormula, tokensCodeLength, Token.arity,
        Token.codeLength, BoolFormula.size]
  | neg formula ih =>
      rw [tokens, forwardScan_append_internal, ih]
      simp [tokens, forwardScan, ForwardScanState.step,
        ForwardScanState.afterFormula, tokensCodeLength, Token.arity,
        Token.codeLength, BoolFormula.size]
      split <;> omega
  | conj left right ihLeft ihRight =>
      rw [tokens, forwardScan_append_internal,
        forwardScan_append_internal, ihLeft, ihRight]
      simp [tokens, forwardScan, ForwardScanState.step,
        ForwardScanState.afterFormula, tokensCodeLength, Token.arity,
        Token.codeLength, BoolFormula.size]
      split <;> omega
  | disj left right ihLeft ihRight =>
      rw [tokens, forwardScan_append_internal,
        forwardScan_append_internal, ihLeft, ihRight]
      simp [tokens, forwardScan, ForwardScanState.step,
        ForwardScanState.afterFormula, tokensCodeLength, Token.arity,
        Token.codeLength, BoolFormula.size]
      split <;> omega

theorem forwardScan_binary_body_internal
    (left right : BoolFormula) :
    forwardScan (tokens left ++ tokens right) ForwardScanState.initial =
      { stackHeight := 2
        tokenCount := left.size + right.size
        bitOffset := tokensCodeLength (tokens left) +
          tokensCodeLength (tokens right)
        lastOneCount := left.size
        lastOneBitOffset := tokensCodeLength (tokens left) } := by
  rw [forwardScan_append_internal, forwardScan_tokens_internal,
    forwardScan_tokens_internal]
  simp [ForwardScanState.initial, ForwardScanState.afterFormula,
    tokensCodeLength]

end FormulaCode

end Complexity
