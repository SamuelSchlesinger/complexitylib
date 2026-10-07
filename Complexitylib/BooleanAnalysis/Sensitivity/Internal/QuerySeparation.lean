/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.DecisionTree
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Separation

/-!
# Query-depth consequences of the sensitivity separation

Combine OpenAI's sensitivity separation with the canonical decision-tree bound
`blockSensitivity f ≤ tree.depth`. These are deductions from the imported
separation, without a claim of research novelty.
-/

public section

namespace Complexity.BooleanAnalysis.Sensitivity.Internal
open DecisionTree

theorem unbounded_quadratic_query_separation (C : ℝ) (hC : 0 < C) :
    ∃ (n : ℕ) (f : BitString n → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y, f x ≠ f y) ∧
      ∀ tree : On n, (∀ x, tree.eval x = f x) →
        C * (sensitivity f : ℝ) ^ 2 < (tree.depth : ℝ) := by
  obtain ⟨n, f, hn, hf, hnc, hb⟩ := unbounded_quadratic_separation C hC
  refine ⟨n, f, hn, hf, hnc, ?_⟩
  intro tree heval
  exact hb.trans_le (by exact_mod_cast blockSensitivity_le_depth f tree heval)

theorem fixed_power_query_separation :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, BitString (n m) → Bool),
        (∀ m : ℕ, 1 ≤ m →
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y, F m x ≠ F m y) ∧
          ∀ tree : On (n m), (∀ x, tree.eval x = F m x) →
            (sensitivity (F m) : ℝ) ^ α ≤ (tree.depth : ℝ)) ∧
        ∀ trees : (m : ℕ) → On (n m),
          (∀ m x, (trees m).eval x = F m x) →
          Filter.Tendsto (fun m => ((trees m).depth : ℝ)) Filter.atTop Filter.atTop := by
  obtain ⟨α, hα, n, F, hall, hlim⟩ := fixed_power_separation
  have hb (m : ℕ) (tree : On (n m)) (heval : ∀ x, tree.eval x = F m x) :
      (blockSensitivityAt (F m) (fun _ => false) : ℝ) ≤ tree.depth := by
    exact_mod_cast (blockSensitivityAt_le_blockSensitivity (F m) _).trans
      (blockSensitivity_le_depth (F m) tree heval)
  refine ⟨α, hα, n, F, ?_, ?_⟩
  · intro m hm
    obtain ⟨hn, hf, hnc, hpow⟩ := hall m hm
    exact ⟨hn, hf, hnc, fun tree heval => hpow.trans (hb m tree heval)⟩
  · intro trees heval
    exact Filter.tendsto_atTop_mono (fun m => hb m (trees m) (heval m)) hlim

end Complexity.BooleanAnalysis.Sensitivity.Internal
