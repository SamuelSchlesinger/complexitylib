/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Defs

/-!
# Signs of the edge and vertex entropy costs

The logarithmic inequalities used here reduce to small integer comparisons.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

/-- The quarter-biased entropy expanded into logarithms of integers. -/
theorem binEntropy_quarter :
    Real.binEntropy (1 / 4) = 2 * Real.log 2 - 3 / 4 * Real.log 3 := by
  have four : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  norm_num [Real.negMulLog_def, Real.log_div]
  rw [four]
  ring

/-- The per-edge cost is nonnegative. -/
theorem edgeCost_nonneg : 0 ≤ edgeCost := by
  have bound := Real.binEntropy_le_log_two (p := (1 / 4 : ℝ))
  have positive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold edgeCost
  linarith

/-- The per-vertex cost is nonnegative because `3 ^ 3 ≤ 2 ^ 5`. -/
theorem vertexCost_nonneg : 0 ≤ vertexCost := by
  have logs : 3 * Real.log 3 ≤ 5 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 3)
      (by norm_num : (3 : ℝ) ^ 3 ≤ 2 ^ 5)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  rw [vertexCost, binEntropy_quarter]
  linarith

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
