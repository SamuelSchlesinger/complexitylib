/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Marked.Defs
public import Complexitylib.Interop.Cslib.FromMultiTape
public import Complexitylib.Interop.Cslib.Guard
import Complexitylib.Interop.Mathlib.TM0.Marked.Internal.Output

/-!
# Marked finite-tape computations transfer to canonical FP

The source input may distinguish its first symbol and use a marker for the
empty word. Output is read through a separate decoder. The existing binary-track
simulator handles these formats with linear initialization and emission cost.
-/

public section

namespace Complexity.MathlibTM0.MarkedMachine

/-- Marked input and a separate output decoder add only linear simulation overhead. -/
theorem computes_cslib (M : MarkedMachine) {input output : List Bool} {time : ℕ}
    (h : M.OutputsWithin input output time) :
    (machine M).ComputesInTimeAndSpace input output
      (2 * input.length + time + output.length + 4)
      ((machine M).spaceUsed ((machine M).initCfg input)
        (2 * input.length + time + output.length + 4)) :=
  computes_proof M h

/-- Polynomial source time and decoded output length imply canonical FP membership. -/
theorem mem_FP {M : MarkedMachine} {f : List Bool → List Bool} {p q : Polynomial ℕ}
    (h : ∀ input, M.OutputsWithin input (f input) (p.eval input.length))
    (hlen : ∀ input, (f input).length ≤ q.eval input.length) : f ∈ FP := by
  let time (input : List Bool) :=
    2 * input.length + p.eval input.length + (f input).length + 4
  refine mem_FP_of_computableInTimeAndSpace
    (p := Polynomial.C 2 * Polynomial.X + p + q + Polynomial.C 4)
    (s := fun input => (machine M).spaceUsed ((machine M).initCfg input) (time input))
    ⟨_, TargetState M, inferInstance, machine M, ?_⟩
  intro input
  refine ⟨time input, ?_, _, le_rfl, M.computes_cslib (h input)⟩
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact Nat.add_le_add_right (Nat.add_le_add_left (hlen input) _) 4

/-- Source bounds only on a regular domain suffice after rejecting malformed inputs. -/
theorem mem_FP_on_dfa {M : MarkedMachine} {σ : Type} [Fintype σ]
    (D : DFA Bool σ) [DecidablePred (· ∈ D.accepts)]
    {f : List Bool → List Bool} {p q : Polynomial ℕ}
    (h : ∀ w ∈ D.accepts, M.OutputsWithin w (f w) (p.eval w.length))
    (hlen : ∀ w ∈ D.accepts, (f w).length ≤ q.eval w.length) :
    (fun w => if w ∈ D.accepts then f w else []) ∈ FP := by
  apply CslibGuard.mem_FP_on_dfa (machine M) D
    (p := Polynomial.C 2 * Polynomial.X + p + q + Polynomial.C 4)
  intro w hw
  refine ⟨2 * w.length + p.eval w.length + (f w).length + 4, ?_, _,
    M.computes_cslib (h w hw)⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  exact Nat.add_le_add_right (Nat.add_le_add_left (hlen w hw) _) 4

end Complexity.MathlibTM0.MarkedMachine
