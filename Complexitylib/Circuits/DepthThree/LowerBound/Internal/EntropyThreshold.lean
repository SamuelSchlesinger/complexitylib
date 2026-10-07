/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Unrestricted depth-three lower bound: entropy threshold

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/EntropyThreshold.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

open Filter
open scoped Topology

namespace DepthThreeLowerBound

/-- The base-two binary entropy function. -/
noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  -(x * Real.log x + (1 - x) * Real.log (1 - x)) / Real.log 2

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy]

theorem binaryEntropy_mul_log_two (x : ℝ) :
    binaryEntropy x * Real.log 2 =
      -(x * Real.log x + (1 - x) * Real.log (1 - x)) := by
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos one_lt_two))

theorem binaryEntropy_nonneg {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 ≤ binaryEntropy x := by
  apply div_nonneg
  · exact neg_nonneg.mpr (add_nonpos
      (Real.mul_log_nonpos hx₀ hx₁)
      (Real.mul_log_nonpos (sub_nonneg.mpr hx₁) (sub_le_self _ hx₀)))
  · exact (Real.log_pos one_lt_two).le

theorem continuous_binaryEntropy : Continuous binaryEntropy := by
  unfold binaryEntropy
  exact ((Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).neg).div_const _

theorem tendsto_binaryEntropy_reciprocal :
    Tendsto (fun r : ℕ => binaryEntropy (1 / (r : ℝ))) atTop (𝓝 0) := by
  simpa only [binaryEntropy_zero, Function.comp_def] using
    (continuous_binaryEntropy.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat

theorem exists_integer_entropy_threshold (F : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℕ, 2 ≤ r ∧ (F : ℝ) * binaryEntropy (1 / (r : ℝ)) ≤ ε := by
  have hlim : Tendsto (fun r : ℕ => (F : ℝ) * binaryEntropy (1 / (r : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul tendsto_binaryEntropy_reciprocal :
        Tendsto (fun r : ℕ => (F : ℝ) * binaryEntropy (1 / (r : ℝ)))
          atTop (𝓝 ((F : ℝ) * 0)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hε))
  exact ⟨max N 2, le_max_right _ _, (hN _ (le_max_left _ _)).le⟩

end DepthThreeLowerBound

end Complexity
