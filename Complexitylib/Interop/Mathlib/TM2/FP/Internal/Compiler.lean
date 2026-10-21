/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM2.FP.Internal.Encoding
public import Complexitylib.Interop.Mathlib.TM2
public import Complexitylib.Interop.Mathlib.TM0.Marked
import Complexitylib.Classes.P.Composition
import Complexitylib.Classes.P.Cobham.Internal.Reverse

/-!
# Canonical FP membership from a Mathlib TM2 string certificate

Compile the source once and supply its exact stack-track input through the
marked copier. The target computes reversal composed with the source function
and reversal. Closure of FP under composition removes those representation
conventions. A source stack-growth bound supplies the required output length.
-/

@[expose] public section

namespace Complexity.MathlibTM2

open Turing

lemma marked_run_eq_exec (M : MathlibTM0.MarkedMachine) (t : ℕ) (c : M.Config) :
    M.run t c = exec (TM0.step M.code) t c := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
      simp only [MathlibTM0.MarkedMachine.run, exec]
      cases TM0.step M.code c <;> simp_all

lemma mem_FP_proof {f : List Bool → List Bool}
    (computer : TM2ComputableInPolyTime id id f) [∀ k, Fintype (computer.tm.Γ k)] :
    f ∈ FP := by
  obtain ⟨m, G, C, _, hG⟩ := exists_tm0_computer computer.tm
  obtain ⟨D, _, hD⟩ := exists_output_length_bound computer.tm
  let M := binaryAdapter computer.tm computer.inputAlphabet computer.outputAlphabet G
  let g (w : List Bool) := (f w.reverse).reverse
  have hg : g ∈ FP := by
    apply MathlibTM0.MarkedMachine.mem_FP (M := M)
      (p := Polynomial.C C * (Polynomial.X + computer.time + 1) ^ 2)
      (q := Polynomial.X + Polynomial.C D * computer.time)
    · intro w
      obtain ⟨u, hu, c, hc, hh, ho⟩ := hG _ _ _ (computer.outputsFun w.reverse)
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
    · intro w
      have hd := hD _ _ _ (computer.outputsFun w.reverse)
      simpa [g] using hd
  have h := mem_FP_comp (mem_FP_comp reverse_mem_FP hg) reverse_mem_FP
  simpa [Function.comp_def, g] using h

end Complexity.MathlibTM2
