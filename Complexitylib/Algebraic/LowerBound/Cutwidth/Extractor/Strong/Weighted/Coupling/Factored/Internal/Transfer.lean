/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Linarith

/-!
# Transferring conditional uniformity across a repair

A repair changes a deterministic continuation by at most its total
variation cost. If the retained marginal changes, comparing to the
actual marginal costs at most the same amount once more. These bounds
hold for arbitrary real weights and also for empty output alphabets.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem repair_uniformSecond_contracts {Tag Out : Type*}
    [Fintype Tag] [Fintype Out] (p q : Tag × Out → ℝ) :
    weightDist (uniformSecondWeight p) (uniformSecondWeight q) ≤ weightDist p q := by
  cases isEmpty_or_nonempty Out with
  | inl h =>
    let := h
    simp [weightDist]
  | inr h =>
    let := h
    have uniform := isProbabilityWeight_uniform Out
    have same : weightDist (uniformSecondWeight p) (uniformSecondWeight q) =
        weightDist (firstWeight p) (firstWeight q) := by
      simp only [weightDist, uniformSecondWeight, uniformExtensionWeight,
        Fintype.sum_prod_type, ← sub_mul, abs_mul]
      simp_rw [abs_of_nonneg (uniform.1 _)]
      simp only [← Finset.mul_sum, uniform.2, mul_one]
    rw [same, ← mapWeight_fst, ← mapWeight_fst]
    exact weightDist_map_le p q Prod.fst

theorem weightDist_uniformSecond_le_of_dist_of_same_first {Tag Out : Type*}
    [Fintype Tag] [Fintype Out] {p q : Tag × Out → ℝ} {ρ ε : ℝ}
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist q (uniformSecondWeight q) ≤ ε)
    (same : firstWeight p = firstWeight q) :
    weightDist p (uniformSecondWeight p) ≤ ρ + ε := by
  have reference : uniformSecondWeight p = uniformSecondWeight q := by
    simp only [uniformSecondWeight, same]
  rw [reference]
  exact (weightDist_triangle p q (uniformSecondWeight q)).trans (add_le_add near uniform)

theorem weightDist_uniformSecond_le_of_dist {Tag Out : Type*}
    [Fintype Tag] [Fintype Out] {p q : Tag × Out → ℝ} {ρ ε : ℝ}
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist q (uniformSecondWeight q) ≤ ε) :
    weightDist p (uniformSecondWeight p) ≤ 2 * ρ + ε := by
  have first := weightDist_triangle p q (uniformSecondWeight q)
  have second := weightDist_triangle p (uniformSecondWeight q) (uniformSecondWeight p)
  have marginal := repair_uniformSecond_contracts q p
  rw [weightDist_comm q p] at marginal
  linarith only [near, uniform, first, second, marginal]

theorem weightDist_uniformSecond_map_le_of_dist_of_same_first {α Tag Out : Type*}
    [Fintype α] [Fintype Tag] [Fintype Out]
    {p q : α → ℝ} {ρ ε : ℝ} (F : α → Tag × Out)
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist (mapWeight F q) (uniformSecondWeight (mapWeight F q)) ≤ ε)
    (same : firstWeight (mapWeight F p) = firstWeight (mapWeight F q)) :
    weightDist (mapWeight F p) (uniformSecondWeight (mapWeight F p)) ≤ ρ + ε :=
  weightDist_uniformSecond_le_of_dist_of_same_first
    ((weightDist_map_le p q F).trans near) uniform same

theorem weightDist_uniformSecond_map_le_of_dist {α Tag Out : Type*}
    [Fintype α] [Fintype Tag] [Fintype Out]
    {p q : α → ℝ} {ρ ε : ℝ} (F : α → Tag × Out)
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist (mapWeight F q) (uniformSecondWeight (mapWeight F q)) ≤ ε) :
    weightDist (mapWeight F p) (uniformSecondWeight (mapWeight F p)) ≤ 2 * ρ + ε :=
  weightDist_uniformSecond_le_of_dist ((weightDist_map_le p q F).trans near) uniform

end Algebraic.Cutwidth.Extractor.Internal
