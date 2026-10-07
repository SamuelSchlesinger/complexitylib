/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MachineLanguage
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageLowerBound

/-!
# Unrestricted depth-three lower bound: main

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Main.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

theorem exists_polynomial_time_language_depth_three_lower_bound_proof :
    ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ),
      0 < C ∧ 0 < a ∧
      (∀ w : List Bool, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) →
          (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (D.gateCount : ℝ) := by
  obtain ⟨M, C, a, hC, ha, hM⟩ := language_polynomial_time
  exact ⟨language, M, C, a, hC, ha, hM, language_depth_three_gate_lower_bound⟩

end DepthThreeLowerBound

end Complexity
