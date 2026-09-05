/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputSources.Defs

/-!
# Constant and primary-input source circuits -- proof internals
-/


public section

namespace Complexity

namespace Circuit

/-- Evaluation over `Basis.andOr2` is `AndOrOp.eval`; stated as an equation so it can be
rewritten without unfolding the basis inside the circuit's type. -/
private theorem andOr2_eval_eq (op : AndOrOp) (n : ℕ)
    (h : (Basis.andOr2.arity op).satisfiedBy n) (inputs : BitString n) :
    Basis.andOr2.eval op n h inputs = AndOrOp.eval op n inputs := rfl

theorem eval_inputSources_internal {inputWidth outputWidth : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (sources : Fin outputWidth → InputSource inputWidth)
    (input : BitString inputWidth) :
    (inputSources sources).eval input =
      fun output => (sources output).eval input := by
  funext output
  unfold Circuit.eval
  change (inputSourceOutputGate (sources output)).eval
      ((inputSources sources).wireValue input) =
    (sources output).eval input
  cases hsource : sources output with
  | constant value =>
      cases value with
      | false =>
          unfold inputSourceOutputGate InputSource.eval Gate.eval
          dsimp only
          erw [andOr2_eval_eq]
          erw [AndOrOp.eval_two_and]
          rw [Circuit.wireValue_of_lt _ _ _ (by
            have hinput : 0 < inputWidth :=
              Nat.pos_of_ne_zero (NeZero.ne inputWidth)
            simp
            omega)]
          simp
      | true =>
          unfold inputSourceOutputGate InputSource.eval Gate.eval
          dsimp only
          erw [andOr2_eval_eq]
          erw [AndOrOp.eval_two_or]
          rw [Circuit.wireValue_of_lt _ _ _ (by
            have hinput : 0 < inputWidth :=
              Nat.pos_of_ne_zero (NeZero.ne inputWidth)
            simp
            omega)]
          simp
  | input coordinate =>
      unfold inputSourceOutputGate InputSource.eval Gate.eval
      simp only [andOr2_eval_eq]
      erw [AndOrOp.eval_two_and]
      simp only [Bool.false_xor]
      rw [Circuit.wireValue_of_lt _ _ _ (by simp)]
      simp

end Circuit

end Complexity
