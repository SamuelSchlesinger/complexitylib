/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.Mathlib.TM0
public import Complexitylib.Interop.Mathlib.TM0.Guard.Defs
import Complexitylib.Interop.Mathlib.TM0.Guard.Internal

/-!
# Polynomial-time functions with a regular input format

A finite Mathlib machine need only satisfy its time and output bounds on the
inputs accepted by a DFA. Checking that format and returning the empty string
on rejection yields a total function in canonical `FP`.
-/

public section

namespace Complexity.MathlibTM0.BinaryMachine

/-- A DFA guard runs the source on valid inputs with linear overhead. -/
theorem guarded_outputsWithin (M : BinaryMachine) {σ : Type} [Fintype σ]
    (D : DFA Bool σ) {w output : List Bool} {time : ℕ}
    (hw : w ∈ D.accepts) (h : M.OutputsWithin w output time) :
    (M.guarded D).OutputsWithin w output (2 * w.length + time + 2) :=
  Guard.accepted M D hw h

/-- A DFA guard rejects malformed inputs with empty output in one scan. -/
theorem guarded_outputsWithin_empty (M : BinaryMachine) {σ : Type} [Fintype σ]
    (D : DFA Bool σ) {w : List Bool} (hw : w ∉ D.accepts) :
    (M.guarded D).OutputsWithin w [] w.length :=
  Guard.rejected M D hw

/-- Polynomial bounds on a regular domain give a total `FP` function, empty elsewhere. -/
theorem mem_FP_on_dfa {M : BinaryMachine} {σ : Type} [Fintype σ]
    (D : DFA Bool σ) [DecidablePred (· ∈ D.accepts)] {f : List Bool → List Bool}
    {p q : Polynomial ℕ}
    (h : ∀ w ∈ D.accepts, M.OutputsWithin w (f w) (p.eval w.length))
    (hlen : ∀ w ∈ D.accepts, (f w).length ≤ q.eval w.length) :
    (fun w => if w ∈ D.accepts then f w else []) ∈ FP := by
  refine mem_FP (M := M.guarded D)
    (p := Polynomial.C 2 * Polynomial.X + p + Polynomial.C 2) (q := q) ?_ ?_
  · intro w
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    by_cases hw : w ∈ D.accepts
    · rw [ite_eq_left hw]
      exact M.guarded_outputsWithin D hw (h w hw)
    · rw [ite_eq_right hw]
      obtain ⟨t, ht, c, hc, hh, ho⟩ := M.guarded_outputsWithin_empty D hw
      exact ⟨t, by lia, c, hc, hh, ho⟩
  · intro w
    split_ifs with hw
    · exact hlen w hw
    · exact Nat.zero_le _

end Complexity.MathlibTM0.BinaryMachine
