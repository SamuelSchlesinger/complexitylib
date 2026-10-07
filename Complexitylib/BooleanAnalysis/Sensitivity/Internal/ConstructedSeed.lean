/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Construction
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Labeling
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.ParameterBounds
public import Complexitylib.BooleanAnalysis.Sensitivity.Internal.Iterates

/-!
# Sensitivity separation: constructed seed

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/ConstructedSeed.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- All construction parameters and labels are supplied unconditionally. -/

noncomputable section
open scoped Classical

namespace Internal

theorem construction_label_count_pos {M : ℕ} (hM : 0 < M) :
    0 < Nat.ceil (Real.sqrt (M : ℝ)) := by
  have h := le_ceil_sqrt_sq M
  by_contra hn
  have he : Nat.ceil (Real.sqrt (M : ℝ)) = 0 := by omega
  rw [he] at h
  norm_num at h
  omega

theorem exists_constructed_seed (d M : ℕ) (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ∃ f : (Fin (constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ)))) → Bool) → Bool,
      0 < constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ))) ∧
      f (fun _ => false) = false ∧ (∃ x y, f x ≠ f y) ∧
      sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1) ∧
      M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false) := by
  have h81 := parameter_ge_eighty_one hd hM
  have hMp : 0 < M := by omega
  have hr := construction_label_count_pos hMp
  obtain ⟨A⟩ := regular_goodLabeling_exists (show 3 ≤ M by omega)
  let f := finalWitness d (regularCyclicTournament M) A
  have hs := finalWitness_sensitivity d (regularCyclicTournament M) A hMp hr
    (parameter_epsilon_budget hd hM)
  have hb := finalWitness_blockSensitivity d (regularCyclicTournament M) A hr
  have hbp : 0 < M ^ 2 * (2 * M ^ 2 + 1) ^ d := by positivity
  have hnc := nonconstant_of_blockSensitivityAt_pos f (fun _ => false) (hbp.trans_le hb)
  exact ⟨f, constructionDimension_pos hMp hr,
    finalWitness_zero d (regularCyclicTournament M) A hr, hnc, hs, hb⟩

end Internal

end

end Complexity.BooleanAnalysis.Sensitivity
