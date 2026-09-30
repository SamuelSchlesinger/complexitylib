/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
public import Complexitylib.Cslib.Circuit.Cut.Defs

/-! # Evaluation lemmas for circuit cuts -/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ} {U : Type*}

/-- Evaluation at a selected gate reads the guess. -/
@[simp] theorem Program.evalCut_mem (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) (guess : cut → U) (j : cut) :
    p.evalCut cut I x guess j = guess j := by
  rw [evalCut, dite_eq_left j.property]

/-- An unselected gate is evaluated from its argument wires. -/
theorem Program.evalCut_not_mem (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) (guess : cut → U)
    (j : Fin g) (hj : j ∉ cut) :
    p.evalCut cut I x guess j = (p.lines j).eval I x (p.evalCut cut I x guess) := by
  rw [evalCut, dite_eq_right hj]
  unfold Line.eval
  congr 1
  funext a
  dsimp only [Function.comp_apply]
  cases (p.lines j).wires a <;> rfl

/-- Supplying the actual values at the cut preserves the evaluation everywhere. -/
theorem Program.evalCut_eq_eval_of_agree (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) (guess : cut → U)
    (agree : ∀ j : cut, guess j = p.eval I x j) :
    p.evalCut cut I x guess = p.eval I x := by
  funext j
  induction hj : j.val using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    subst hj
    by_cases hcut : j ∈ cut
    · exact (p.evalCut_mem cut I x guess ⟨j, hcut⟩).trans (agree ⟨j, hcut⟩)
    · rw [p.evalCut_not_mem cut I x guess j hcut, ← p.lines_eval I x j]
      unfold Line.eval
      congr 1
      funext a
      dsimp only [Function.comp_apply]
      have hlt := p.lines_wires_lt j a
      cases hw : (p.lines j).wires a with
      | input i => rfl
      | gate l =>
        rw [hw] at hlt
        exact ih l.val (by simpa using hlt) l rfl

end Cslib.Circuits
