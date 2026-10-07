/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Machine
public import Complexitylib.Circuits.DepthThree.LowerBound.Balanced
public import Complexitylib.Classes.P.Defs
import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Uniform

/-!
# A balanced polynomial-time language with unrestricted depth-three hardness

These statements use complexitylib's canonical `P` and `FP`, through the checked machine
simulation. Circuit gates are counted in the source's unrestricted shared three-layer model.
-/

public section

namespace Complexity.DepthThreeLowerBound

/-- OpenAI's explicit depth-three hard language belongs to the canonical class `P`. -/
theorem language_mem_P : {w | language w = true} ∈ P :=
  language_mem_P_proof

/-- Its one-bit verdict is a polynomial-time function in the canonical `FP`. -/
theorem language_eval_mem_FP : (fun w => [language w]) ∈ FP :=
  language_eval_mem_FP_proof

/-- Balanced padding of the hard language also belongs to the canonical class `P`. -/
theorem balancedLanguage_mem_P : {w | balancedLanguage w = true} ∈ P :=
  balancedLanguage_mem_P_proof

/-- An exactly balanced language in canonical `P` needs every fixed square-root exponential
number of gates in both unrestricted depth-three polarities. -/
theorem exists_balanced_language_in_P_depth_three_lower_bound :
    ∃ L : List Bool → Bool, {w | L w = true} ∈ P ∧
      (∀ n, (Finset.univ.filter fun x : Cube (Fin (n + 1)) => L (List.ofFn x) = true).card =
        2 ^ n) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D : Circuit3 (Fin (n + 1)),
        (D.Computes (fun x => L (List.ofFn x)) ∨
          D.ComputesDual (fun x => L (List.ofFn x))) →
          (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (D.gateCount : ℝ) :=
  exists_balanced_language_in_P_depth_three_lower_bound_proof

end Complexity.DepthThreeLowerBound
