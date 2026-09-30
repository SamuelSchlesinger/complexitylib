/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
public import Complexitylib.Cslib.Circuit.Cut.Defs
public import Complexitylib.Cslib.Circuit.Cut.Internal

/-!
# Unique consistent values at a circuit cut

For any selected gates, there is exactly one consistent assignment of guessed
values: the actual evaluation restricted to those gates. Consequently a
circuit's output can be described by existentially guessing the cut values,
checking the selected gates' equations, and evaluating the output with those
guesses. This is a semantic certificate theorem; it makes no formula-size or
communication-cost claim.

These are generic extensions of CSLib's `Program` and `Circuit`, suitable for
upstreaming. Repeated uses of a selected gate read the same guessed value.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n m g : ℕ} {U : Type*}

/-- A consistent guess recovers all gate values, including unselected gates. -/
theorem Program.evalCut_eq_eval_of_consistent (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) (guess : cut → U)
    (consistent : p.CutConsistent cut I x guess) :
    p.evalCut cut I x guess = p.eval I x := by
  apply p.eq_eval_of_forall_lines_eval
  intro j
  by_cases hj : j ∈ cut
  · exact (consistent ⟨j, hj⟩).trans (p.evalCut_mem cut I x guess ⟨j, hj⟩).symm
  · exact (p.evalCut_not_mem cut I x guess j hj).symm

/-- Consistency is equivalent to agreement with the actual values at the cut. -/
theorem Program.cutConsistent_iff (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) (guess : cut → U) :
    p.CutConsistent cut I x guess ↔ ∀ j : cut, guess j = p.eval I x j := by
  constructor
  · intro consistent j
    rw [← p.evalCut_mem cut I x guess j,
      p.evalCut_eq_eval_of_consistent cut I x guess consistent]
  · intro agree j
    rw [p.evalCut_eq_eval_of_agree cut I x guess agree, p.lines_eval, agree j]

/-- Every input has exactly one consistent cut certificate. -/
theorem Program.existsUnique_cutConsistent (p : Program σ n g) (cut : Finset (Fin g))
    (I : Interpretation σ U) (x : Fin n → U) :
    ∃! guess : cut → U, p.CutConsistent cut I x guess := by
  refine ⟨fun j => p.eval I x j, ?_, ?_⟩
  · exact (p.cutConsistent_iff cut I x _).mpr fun _ => rfl
  · intro guess consistent
    exact funext ((p.cutConsistent_iff cut I x guess).mp consistent)

/-- Guessing and checking the cut values gives exactly the original circuit's output. -/
theorem Circuit.eval_eq_iff_exists_cut (c : Circuit σ n m) (cut : Finset (Fin c.size))
    (I : Interpretation σ U) (x : Fin n → U) (y : Fin m → U) :
    c.eval I x = y ↔ ∃ guess : cut → U,
      c.program.CutConsistent cut I x guess ∧
      Wire.elim x (c.program.evalCut cut I x guess) ∘ c.outputs = y := by
  constructor
  · intro hy
    obtain ⟨guess, consistent, _⟩ := c.program.existsUnique_cutConsistent cut I x
    refine ⟨guess, consistent, ?_⟩
    rw [c.program.evalCut_eq_eval_of_consistent cut I x guess consistent]
    exact hy
  · rintro ⟨guess, consistent, hy⟩
    rw [c.program.evalCut_eq_eval_of_consistent cut I x guess consistent] at hy
    exact hy

end Cslib.Circuits
