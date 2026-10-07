/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionPathData
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.ReversePathEncoding
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Unrestricted depth-three lower bound: restriction expected cost

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionExpectedCost.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [Fintype V] [Fintype I]

theorem pathCoveredCount_eq_of_support (C : I → Clause V) (σ : Restriction V)
    (P : List I) (x : Cube (Live σ))
    (hn : ∀ i ∈ P, (C i).Normalized)
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) :
    pathCoveredCount C σ P h =
      coveredCount (fun i => (C i).scope) (liveSet σ)
        (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) := by
  have hc : pathCompatible C σ P := ⟨x, hx⟩
  have hZ : ∀ v ∈ pathFinalSet C σ P,
      fill σ (pathCenter C σ P) v = fill σ x v := by
    exact (simultaneous_restricted_violation_iff C σ (liveSet σ)
      (fun v => mem_liveSet σ v) P (pathCenter C σ P) x hn hx).mp
        (pathCenter_support C σ P hc)
  unfold pathCoveredCount
  apply coveredCount_eq_on_larger_cylinder C (liveSet σ)
    (pathPrefixSet C σ P h) (pathFinalSet C σ P)
    (fill σ (pathCenter C σ P)) (fill σ x)
    (pathPrefixSet_subset_final C σ P h) hZ
  intro v hv
  exact fill_agree_outside_live σ (pathCenter C σ P) x v
    (by simpa only [mem_liveSet] using hv)

theorem pathWeight_eq_coveredPathWeight_of_support (C : I → Clause V)
    (σ : Restriction V) (P : List I) (x : Cube (Live σ))
    (hn : ∀ i ∈ P, (C i).Normalized)
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true) :
    pathWeight C σ P = coveredPathWeight (fun i => (C i).scope) (liveSet σ)
      (fun i => (C i).violation (fill σ x)) P := by
  unfold pathWeight coveredPathWeight
  apply Finset.prod_congr rfl
  intro h hh
  exact congrArg (fun n : ℕ => (n : ℝ)⁻¹)
    (pathCoveredCount_eq_of_support C σ P x hn hx h)

theorem pathWeight_eq_finiteAvg_supported (C : I → Clause V)
    (σ : Restriction V) (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) :
    (if pathCompatible C σ P then pathWeight C σ P else 0) =
      finiteAvg (fun x : Cube (Live σ) =>
        if ∀ i ∈ P, (C i).violation (fill σ x) = true then
          (2 : ℝ) ^ (pathFinalSet C σ P).card *
            coveredPathWeight (fun i => (C i).scope) (liveSet σ)
              (fun i => (C i).violation (fill σ x)) P
        else 0) := by
  by_cases hc : pathCompatible C σ P
  · rw [ite_eq_left hc]
    symm
    calc
      _ = finiteAvg (fun x : Cube (Live σ) =>
          ((2 : ℝ) ^ (pathFinalSet C σ P).card * pathWeight C σ P) *
            indicator (decide (∀ i ∈ P, (C i).violation (fill σ x) = true))) := by
        apply finiteAvg_congr
        intro x
        by_cases hx : ∀ i ∈ P, (C i).violation (fill σ x) = true
        · rw [ite_eq_left hx, ← pathWeight_eq_coveredPathWeight_of_support C σ P x hn hx]
          rw [decide_eq_true hx, indicator_true, mul_one]
        · rw [ite_eq_right hx, decide_eq_false hx, indicator_false, mul_zero]
      _ = ((2 : ℝ) ^ (pathFinalSet C σ P).card * pathWeight C σ P) *
          ((2 : ℝ) ^ (pathFinalSet C σ P).card)⁻¹ := by
        rw [finiteAvg_const_mul, path_cylinder_probability C σ P hn hc]
      _ = pathWeight C σ P := by
        have htwo : (2 : ℝ) ^ (pathFinalSet C σ P).card ≠ 0 :=
          pow_ne_zero _ (by norm_num)
        calc
          _ = pathWeight C σ P *
              ((2 : ℝ) ^ (pathFinalSet C σ P).card *
                ((2 : ℝ) ^ (pathFinalSet C σ P).card)⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ htwo, mul_one]
  · rw [ite_eq_right hc]
    symm
    calc
      _ = finiteAvg (fun _ : Cube (Live σ) => (0 : ℝ)) := by
        apply finiteAvg_congr
        intro x
        have hx : ¬ ∀ i ∈ P, (C i).violation (fill σ x) = true :=
          fun hx => hc ⟨x, hx⟩
        simp only [ite_eq_right hx]
      _ = 0 := finiteAvg_zero

/-- Evaluate the path-expansion cost on a full assignment. -/
def fullAssignmentPathCost (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (j : ℕ) (y : Cube V) : ℝ :=
  ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b j,
    if ∀ i ∈ P, (C i).violation y = true then
      (2 : ℝ) ^ (pathFinalSet C σ P).card *
        coveredPathWeight (fun i => (C i).scope) (liveSet σ)
          (fun i => (C i).violation y) P
    else 0

theorem pathCost_eq_finiteAvg_supported (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (j : ℕ) (hn : ∀ i, (C i).Normalized) :
    pathCost C b σ j = finiteAvg (fun x : Cube (Live σ) =>
      fullAssignmentPathCost C b σ j (fill σ x)) := by
  unfold pathCost fullAssignmentPathCost
  rw [finiteAvg_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact pathWeight_eq_finiteAvg_supported C σ P (fun i _ => hn i)

theorem restrictionAvg_pathCost_reweight (C : I → Clause V) (p : ℝ)
    (b j : ℕ) (hn : ∀ i, (C i).Normalized) :
    restrictionAvg p (fun σ => pathCost C b σ j) =
      finiteAvg (fun y : Cube V =>
        ∑ T : Finset V, bernoulliWeight p T *
          fullAssignmentPathCost C b (maskRestriction T y) j y) := by
  calc
    _ = restrictionAvg p (fun σ => finiteAvg (fun x : Cube (Live σ) =>
        fullAssignmentPathCost C b σ j (fill σ x))) := by
      unfold restrictionAvg
      apply Finset.sum_congr rfl
      intro σ hσ
      exact congrArg (fun t : ℝ => restrictionWeight p σ * t)
        (pathCost_eq_finiteAvg_supported C b σ j hn)
    _ = _ := restrictionAvg_fill_reweight p
      (fun σ y => fullAssignmentPathCost C b σ j y)

theorem restrictionAvg_pathCost_le (C : I → Clause V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (b k j : ℕ)
    (hn : ∀ i, (C i).Normalized) (hwidth : ∀ i, (C i).scope.card ≤ k) :
    restrictionAvg p (fun σ => pathCost C b σ j) ≤
      (reverseTheta (2 * p / (1 - p)) b k) ^ j := by
  rw [restrictionAvg_pathCost_reweight C p b j hn]
  calc
    _ ≤ finiteAvg (fun _ : Cube V => (reverseTheta (2 * p / (1 - p)) b k) ^ j) := by
      apply finiteAvg_mono
      intro y
      simpa only [fullAssignmentPathCost, pathFinalSet, liveSet_maskRestriction]
        using weighted_supported_paths_le p hp0 hp1 b k (fun i => (C i).scope)
          hwidth (fun i => (C i).violation y) j
    _ = _ := finiteAvg_const _

theorem restrictionAvg_restrictionCost_le_sum (C : I → Clause V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (b k : ℕ)
    (hn : ∀ i, (C i).Normalized) (hwidth : ∀ i, (C i).scope.card ≤ k) :
    restrictionAvg p (fun σ => restrictionCost C b σ) ≤
      ∑ j ∈ Finset.range (Fintype.card V / (b + 1) + 1),
        (reverseTheta (2 * p / (1 - p)) b k) ^ j := by
  have hsum : restrictionAvg p (fun σ => restrictionCost C b σ) =
      ∑ j ∈ Finset.range (Fintype.card V / (b + 1) + 1),
        restrictionAvg p (fun σ => pathCost C b σ j) := by
    unfold restrictionAvg restrictionCost
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hsum]
  exact Finset.sum_le_sum fun j hj =>
    restrictionAvg_pathCost_le C p hp0 hp1 b k j hn hwidth

theorem restrictionAvg_restrictionCost_le (C : I → Clause V) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (b k : ℕ)
    (hn : ∀ i, (C i).Normalized) (hwidth : ∀ i, (C i).scope.card ≤ k)
    (hθ : reverseTheta (2 * p / (1 - p)) b k < 1) :
    restrictionAvg p (fun σ => restrictionCost C b σ) ≤
      (1 - reverseTheta (2 * p / (1 - p)) b k)⁻¹ := by
  have hα : 0 ≤ 2 * p / (1 - p) :=
    div_nonneg (mul_nonneg (by norm_num) hp0.le) (sub_nonneg.mpr hp1.le)
  have hθ0 := reverseTheta_nonneg hα b k
  refine (restrictionAvg_restrictionCost_le_sum C p hp0 hp1 b k hn hwidth).trans ?_
  simpa only [Nat.Ico_zero_eq_range, pow_zero, one_div] using
    (geom_sum_Ico_le_of_lt_one hθ0 hθ
      (m := 0) (n := Fintype.card V / (b + 1) + 1))

end DepthThreeLowerBound

end

end Complexity
