/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.SeedAmplification

/-!
# Sensitivity separation: separation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/Separation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- Quantitative, unbounded quadratic, and fixed-power separations of sensitivity. -/

noncomputable section
open scoped Classical

namespace Internal

theorem quantitative_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  let M : ℕ := 9 ^ (d + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨f, hn, hf, hnc, hs, hb⟩ := exists_constructed_seed d M hd (by rfl)
  exact ⟨_, f, hn, hf, hnc, quantitative_ratio_of_bounds f d M hM hnc hs hb⟩

theorem unbounded_quadratic_separation (C : ℝ) (hC : 0 < C) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (blockSensitivity f : ℝ) := by
  obtain ⟨d, hd, hlarge⟩ := ((Filter.eventually_ge_atTop (1 : ℕ)).and
    (quantitative_ratio_tendsto.eventually_gt_atTop (max C 0))).exists
  rw [max_eq_left hC.le] at hlarge
  obtain ⟨n, f, hn, hf, hnc, hratio⟩ := quantitative_separation d hd
  have hs : (0 : ℝ) < sensitivity f := by
    exact_mod_cast sensitivity_pos_of_nonconstant f hnc
  exact ⟨n, f, hn, hf, hnc, (lt_div_iff₀ (pow_pos hs 2)).mp (hlarge.trans_le hratio)⟩

theorem fixed_power_separation :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, (Fin (n m) → Bool) → Bool),
        (∀ m : ℕ, 1 ≤ m →
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y : Fin (n m) → Bool, F m x ≠ F m y) ∧
          (sensitivity (F m) : ℝ) ^ α ≤
            (blockSensitivityAt (F m) (fun _ => false) : ℝ)) ∧
        Filter.Tendsto
          (fun m : ℕ => (blockSensitivityAt (F m) (fun _ => false) : ℝ))
          Filter.atTop Filter.atTop := by
  obtain ⟨α, hα, n, F, hall, hlim⟩ := constructed_power_family
  refine ⟨α, hα, n, F, ?_, hlim⟩
  intro m _
  obtain ⟨hn, hf, hnc, hpow, _⟩ := hall m
  exact ⟨hn, hf, hnc, hpow⟩

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity
