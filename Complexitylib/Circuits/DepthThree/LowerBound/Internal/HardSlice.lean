/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSliceEventual
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.WideCorrelation

/-!
# Unrestricted depth-three lower bound: hard slice

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HardSlice.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem exists_language_slice_small_correlations (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ α : Fin n → Sum (Fin (dataDimension n)) Bool,
        ∀ H : CNF (Fin (dataDimension n)),
          H.WidthAtMost (degreeCutoff s (dataDimension n)) →
          |finiteAvg (fun x =>
            sign (language (List.ofFn (GateInput.assignment α x))) * indicator (H.eval x))| ≤
            6 * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 16) := by
  let B : ℝ := 64 * (s + 1)
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨b, hb, D, hD, hparams⟩ := exists_final_parameter_width B s hB hs
  obtain ⟨Ng, hNg, hgood⟩ := exists_good_language_slice_eventually b hb B hB
  refine ⟨max Ng (5 * D), hNg.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hng : Ng ≤ n := (le_max_left _ _).trans hn
  have hnd : 5 * D ≤ n := (le_max_right _ _).trans hn
  have hDd : D ≤ dataDimension n := by unfold dataDimension; omega
  obtain ⟨hp0, hphalf, hθ⟩ := hparams (dataDimension n) hDd
  have hp1 : liveProbability B (dataDimension n) < 1 := by linarith
  have hθ' : restrictionTheta (degreeCutoff s (dataDimension n)) b
      (liveProbability B (dataDimension n)) ≤ 1 / 2 := by
    simpa only [restrictionTheta_eq_reverseTheta] using hθ
  obtain ⟨α, hα⟩ := hgood n hng
  refine ⟨α, ?_⟩
  exact wide_correlation_of_good_restrictions hp0 hp1
    (Real.rpow_nonneg (by norm_num) _) b (degreeCutoff s (dataDimension n)) hb hθ'
    (fun x => language (List.ofFn (GateInput.assignment α x))) hα

end DepthThreeLowerBound

end

end Complexity
