/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Linarith

/-!
# Bounded statistics and the distance form of strong extraction

Center a statistic in `[0,1]` at one half; equal total masses cancel the
constant contribution. The finite-test characterization then identifies
weighted strong extraction with distance from the uniform joint law.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightExpectation_sub_le_dist {α : Type*} [Fintype α]
    (p q f : α → ℝ) (mass : ∑ x, p x = ∑ x, q x)
    (lower : ∀ x, 0 ≤ f x) (upper : ∀ x, f x ≤ 1) :
    |(∑ x, p x * f x) - ∑ x, q x * f x| ≤ weightDist p q := by
  have balance : ∑ x, (p x - q x) = 0 := by
    rw [Finset.sum_sub_distrib, mass, sub_self]
  have center : ∑ x, (p x - q x) * f x =
      ∑ x, (p x - q x) * (f x - 1 / 2) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, balance, zero_mul, sub_zero]
  have bounded (x : α) : |f x - 1 / 2| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [lower x, upper x]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [center]
  calc
    |∑ x, (p x - q x) * (f x - 1 / 2)| ≤
        ∑ x, |(p x - q x) * (f x - 1 / 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |p x - q x| * (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (bounded x) (abs_nonneg _)
    _ = weightDist p q := by
      rw [← Finset.sum_mul]
      simp only [weightDist, mul_one_div]

private theorem weightedSeededOutput_dist_le_iff_tests {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    (p : α → ℝ) (E : α → Seed → Ω) (probability : IsProbabilityWeight p) {ε : ℝ} :
    weightDist (weightedSeededOutput p E)
        (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) ≤ ε ↔
      ∀ T : Finset (Seed × Ω),
        |weightedSeededTestProb p E T - uniformSeededTestProb T| ≤ ε := by
  have actual := probability.weightedSeededOutput E
  have ideal := isProbabilityWeight_seedFamilyWeight (fun _ : Seed => uniformWeight Ω)
    (fun _ => isProbabilityWeight_uniform Ω)
  simpa only [weightTestProb_weightedSeededOutput, weightTestProb_seedFamilyWeight_uniform] using
    weightDist_le_iff_tests (weightedSeededOutput p E)
      (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) (actual.2.trans ideal.2.symm)

theorem weightedStrongSeededExtractor_dist_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    {p : α → ℝ} (probability : IsProbabilityWeight p) (cap : CappedWeight p K) :
    weightDist (weightedSeededOutput p E)
      (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) ≤ ε :=
  (weightedSeededOutput_dist_le_iff_tests p E probability).mpr (extract p probability cap)

theorem weightedStrongSeededExtractor_iff_dist_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    (E : α → Seed → Ω) (K : Nat) (ε : ℝ) :
    WeightedStrongSeededExtractor E K ε ↔
      ∀ p : α → ℝ, IsProbabilityWeight p → CappedWeight p K →
        weightDist (weightedSeededOutput p E)
          (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) ≤ ε := by
  constructor
  · intro extract p probability cap
    exact weightedStrongSeededExtractor_dist_le extract probability cap
  · intro distance p probability cap
    exact (weightedSeededOutput_dist_le_iff_tests p E probability).mp (distance p probability cap)

end Algebraic.Cutwidth.Extractor.Internal
