/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputProjection.Defs

/-!
# Primary-input projection circuits -- proof internals
-/


public section

namespace Complexity

namespace Circuit

/-- Evaluation over `Basis.andOr2` is `AndOrOp.eval`; stated as an equation so it can be
rewritten without unfolding the basis inside the circuit's type. -/
private theorem andOr2_eval_eq (op : AndOrOp) (n : ℕ)
    (h : (Basis.andOr2.arity op).satisfiedBy n) (inputs : BitString n) :
    Basis.andOr2.eval op n h inputs = AndOrOp.eval op n inputs := rfl

theorem eval_projectInputs_internal {N M : ℕ} [NeZero N] [NeZero M]
    (mapInput : Fin M → Fin N) (input : BitString N) :
    (projectInputs mapInput).eval input = input ∘ mapInput := by
  funext output
  unfold Circuit.eval projectInputs inputProjectionOutputGate Gate.eval
  simp only [andOr2_eval_eq]
  rw [AndOrOp.eval_two_and]
  simp only [Bool.false_xor]
  rw [Circuit.wireValue_of_lt _ _ _ (by simp)]
  simp

end Circuit

end Complexity
