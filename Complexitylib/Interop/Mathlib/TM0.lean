/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Defs
public import Complexitylib.Interop.Cslib.FromMultiTape
import Complexitylib.Interop.Mathlib.TM0.Internal.Output

/-!
# Finite Mathlib TM0 string computations transfer to canonical FP

The binary CSLib simulator copies its input to symbol tracks, runs the source,
then emits the complete right-of-head output. Its time bound is
`2 * input.length + sourceTime + output.length + 4`.

Polynomial source time and output length on every binary input therefore imply
membership in complexitylib's canonical `FP`. The complete input/output contract
is required; a runtime bound restricted to well-formed inputs needs a separate
validation or totalization argument before applying the function theorem.
-/

public section

namespace Complexity.MathlibTM0

/-- The binary simulator preserves the full source output with explicit linear overhead. -/
theorem BinaryMachine.computes_cslib (M : BinaryMachine) {input output : List Bool} {time : ℕ}
    (h : M.OutputsWithin input output time) :
    (machine M).ComputesInTimeAndSpace input output
      (2 * input.length + time + output.length + 4)
      ((machine M).spaceUsed ((machine M).initCfg input)
        (2 * input.length + time + output.length + 4)) :=
  computes_proof M h

/-- Polynomial source time and complete output length give canonical `FP` membership. -/
theorem BinaryMachine.mem_FP {M : BinaryMachine} {f : List Bool → List Bool}
    {p q : Polynomial ℕ}
    (h : ∀ input, M.OutputsWithin input (f input) (p.eval input.length))
    (hlen : ∀ input, (f input).length ≤ q.eval input.length) : f ∈ FP := by
  let time (input : List Bool) :=
    2 * input.length + p.eval input.length + (f input).length + 4
  refine mem_FP_of_computableInTimeAndSpace
    (p := Polynomial.C 2 * Polynomial.X + p + q + Polynomial.C 4)
    (s := fun input => (machine M).spaceUsed ((machine M).initCfg input) (time input))
    ⟨_, Control M.State, inferInstance, machine M, ?_⟩
  intro input
  refine ⟨time input, ?_, _, le_rfl, M.computes_cslib (h input)⟩
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact Nat.add_le_add_right (Nat.add_le_add_left (hlen input) _) 4

end Complexity.MathlibTM0
