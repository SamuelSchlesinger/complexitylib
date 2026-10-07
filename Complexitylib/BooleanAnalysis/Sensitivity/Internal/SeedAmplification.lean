/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.ConstructedSeed
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.PowerAmplification
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.SeparationArithmetic

/-!
# Sensitivity separation: seed amplification

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/SeedAmplification.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- The depth-nine seed gives a fixed exponent and explicit ratios. -/

noncomputable section
open scoped Classical

namespace Internal

theorem constructed_power_family :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, (Fin (n m) → Bool) → Bool),
        (∀ m : ℕ,
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y, F m x ≠ F m y) ∧
          (sensitivity (F m) : ℝ) ^ α ≤ (blockSensitivityAt (F m) (fun _ => false) : ℝ) ∧
          ((128 : ℝ) / 121) ^ m ≤
            (blockSensitivity (F m) : ℝ) / (sensitivity (F m) : ℝ) ^ 2) ∧
        Filter.Tendsto
          (fun m : ℕ => (blockSensitivityAt (F m) (fun _ => false) : ℝ))
          Filter.atTop Filter.atTop := by
  let M : ℕ := 9 ^ 10
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨f, _, hf, _, hs, hb⟩ := exists_constructed_seed 9 M (by norm_num) (by rfl)
  change sensitivity f ≤ 22 * M ^ 10 at hs
  obtain ⟨hA, hB⟩ := depth_nine_seed_gap M hM
  obtain ⟨hα, hall, hlim⟩ := power_amplification f hf (22 * M ^ 10)
    (M ^ 2 * (2 * M ^ 2 + 1) ^ 9) hs hb hA hB
  refine ⟨_, hα, _, (fun m => iterateFin f m), ?_, hlim⟩
  intro m
  obtain ⟨hn, hzero, hnc, hpow, hratio⟩ := hall m
  refine ⟨hn, hzero, hnc, hpow, ?_⟩
  apply le_trans _ hratio
  apply pow_le_pow_left₀ (by norm_num)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    using depth_nine_seed_ratio hMr

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity
