/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.FP.Internal.Compiler
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.Cobham.Internal.Reverse
import Mathlib.Computability.NFA

/-!
# Regular-domain TM2 computations

Reverse the input DFA as well as the string representation, guard the marked
simulator, and then use polynomial-time reversal to restore the original order.
The source need only have a runtime bound on accepted strings.
-/

@[expose] public section

namespace Complexity.MathlibTM2

open Turing

lemma mem_FP_on_dfa_proof {f : List Bool → List Bool}
    (computer : TM2ComputableAux Bool Bool) [∀ k, Fintype (computer.tm.Γ k)]
    {σ : Type} [Fintype σ] (D : DFA Bool σ) [DecidablePred (· ∈ D.accepts)]
    {p : Polynomial ℕ}
    (h : ∀ w ∈ D.accepts, TM2OutputsInTime computer.tm (w.map computer.inputAlphabet.symm)
      (some ((f w).map computer.outputAlphabet.symm)) (p.eval w.length)) :
    (fun w => if w ∈ D.accepts then f w else []) ∈ FP := by
  classical
  obtain ⟨m, G, C, _, hG⟩ := exists_tm0_computer computer.tm
  obtain ⟨L, _, hL⟩ := exists_output_length_bound computer.tm
  let M := binaryAdapter computer.tm computer.inputAlphabet computer.outputAlphabet G
  let D' := D.toNFA.reverse.toDFA
  have accepts (w : List Bool) : w ∈ D'.accepts ↔ w.reverse ∈ D.accepts := by
    simp [D']
  let g (w : List Bool) := (f w.reverse).reverse
  have hg : (fun w => if w ∈ D'.accepts then g w else []) ∈ FP := by
    apply MathlibTM0.MarkedMachine.mem_FP_on_dfa (M := M) D'
      (p := Polynomial.C C * (Polynomial.X + p + 1) ^ 2)
      (q := Polynomial.X + Polynomial.C L * p)
    · intro w hw
      have hs := h w.reverse ((accepts w).mp hw)
      obtain ⟨u, hu, c, hc, hh, ho⟩ := hG _ _ _ hs
      refine ⟨u, ?_, c, ?_, hh, ?_⟩
      · simpa using hu
      · rw [marked_run_eq_exec]
        dsimp only [M]
        rw [binaryAdapter_input]
        exact hc
      · intro j
        change ((c.Tape.nth j).2 computer.tm.k₁).map computer.outputAlphabet = _
        rw [ho, decode_trInit]
        simp [g, List.map_reverse]
    · intro w hw
      have hl := hL _ _ _ (h w.reverse ((accepts w).mp hw))
      simpa [g] using hl
  have hr := mem_FP_comp (mem_FP_comp reverse_mem_FP hg) reverse_mem_FP
  have heq :
      (List.reverse ∘ (fun w => if w ∈ D'.accepts then g w else []) ∘ List.reverse) =
        (fun w => if w ∈ D.accepts then f w else []) := by
    funext w
    by_cases hw : w ∈ D.accepts <;> simp [Function.comp_def, accepts, hw, g]
  rw [heq] at hr
  exact hr

end Complexity.MathlibTM2
