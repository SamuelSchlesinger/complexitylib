/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Machine
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MachineLanguage
public import Complexitylib.Circuits.DepthThree.LowerBound.Balanced
public import Complexitylib.Classes.P.Verdict
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Padding


/-!
# Uniform polynomial time for the hard language and its balanced padding

Apply the finite-alphabet simulator to the source's explicit decider, then use the existing
`P` verdict characterization and balanced-padding `FP` closure.
-/

public section

namespace Complexity.DepthThreeLowerBound

lemma language_mem_P_proof : {w | language w = true} ∈ P := by
  obtain ⟨M, C, a, _, _, hM⟩ := language_polynomial_time
  apply FiniteMultiTapeMachine.mem_P (M := M)
    (p := Polynomial.C C * (Polynomial.X + 1) ^ a)
  simpa using hM

lemma language_eval_mem_FP_proof : (fun w => [language w]) ∈ FP := by
  obtain ⟨g, hg, he⟩ := exists_decisionFn_of_mem_P language_mem_P_proof
  have hge : g = language := by
    funext w
    exact Bool.eq_iff_iff.mpr (he w).symm
  simpa [hge] using hg

lemma balancedLanguage_mem_P_proof : {w | balancedLanguage w = true} ∈ P := by
  apply mem_P_of_decisionFn_bool (g := balancedLanguage) _ (fun _ => Iff.rfl)
  exact Algebraic.Cutwidth.balancePadEval_mem_FP language_eval_mem_FP_proof

lemma exists_balanced_language_in_P_depth_three_lower_bound_proof :
    ∃ L : List Bool → Bool, {w | L w = true} ∈ P ∧
      (∀ n, (Finset.univ.filter fun x : Cube (Fin (n + 1)) => L (List.ofFn x) = true).card =
        2 ^ n) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D : Circuit3 (Fin (n + 1)),
        (D.Computes (fun x => L (List.ofFn x)) ∨
          D.ComputesDual (fun x => L (List.ofFn x))) →
          (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (D.gateCount : ℝ) := by
  refine ⟨balancedLanguage, balancedLanguage_mem_P_proof, ?_, ?_⟩
  · intro n
    simpa only [balancedLanguage_ofFn, Algebraic.Cutwidth.accepting] using
      balancedFamily_card n
  · simpa only [balancedLanguage_ofFn] using balancedFamily_both_polarities

end Complexity.DepthThreeLowerBound
