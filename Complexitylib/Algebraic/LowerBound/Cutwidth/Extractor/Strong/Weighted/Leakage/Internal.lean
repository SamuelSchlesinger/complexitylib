/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Expectation
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Algebra.BigOperators.Field

/-!
# Row averaging for extraction after leakage

Retaining the row tag makes the joint distance exactly the marginal-weighted
average of row distances. Rows of mass at least `K * μ` obey the extractor's
conditional cap. Every smaller row is charged its mass, at most `K * μ`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightDist_tagged_seededOutput {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    (E : Source → Seed → Out) (w : Tag → ℝ) (p : Tag → Source → ℝ)
    (nonnegative : ∀ t, 0 ≤ w t) :
    weightDist
      (weightedSeededOutput (fun tx : Tag × Source => w tx.1 * p tx.1 tx.2)
        (fun tx y => (tx.1, E tx.2 y)))
      (seedFamilyWeight (fun _ : Seed => uniformExtensionWeight Out w)) =
        ∑ t, w t * weightDist (weightedSeededOutput (p t) E)
          (seedFamilyWeight (fun _ : Seed => uniformWeight Out)) := by
  classical
  have fiber (y : Seed) :
      weightDist
        (mapWeight (fun tx : Tag × Source => (tx.1, E tx.2 y))
          (fun tx => w tx.1 * p tx.1 tx.2))
        (uniformExtensionWeight Out w) =
          ∑ t, w t * weightDist (mapWeight (fun x => E x y) (p t))
            (uniformWeight Out) := by
    rw [mapWeight_tagged (fun _ x => E x y) w p]
    exact weightDist_tagged_mixture w
      (fun t => mapWeight (fun x => E x y) (p t)) (fun _ => uniformWeight Out) nonnegative
  rw [weightDist_weightedSeededOutput_seedFamilyWeight]
  simp_rw [fiber]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.mul_sum, mul_div_assoc,
    ← weightDist_weightedSeededOutput_seedFamilyWeight (p t) E
      (fun _ : Seed => uniformWeight Out)]

theorem weightedStrongSeededExtractor_leakage_dist_le {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : Source → Seed → Out} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : Tag × Source → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, p (t, x) ≤ μ t) :
    weightDist (weightedSeededOutput p (fun tx y => (tx.1, E tx.2 y)))
      (seedFamilyWeight (fun _ : Seed => uniformExtensionWeight Out (firstWeight p))) ≤
        ε + (K : ℝ) * ∑ t, μ t := by
  classical
  obtain ⟨tx, _⟩ := probability.exists_pos
  let : Nonempty Source := ⟨tx.2⟩
  have row (t : Tag) : IsProbabilityWeight (conditionalWeight p t) :=
    probability.conditionalWeight t
  have marginal := probability.first
  have threshold : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have row_bound (t : Tag) :
      firstWeight p t * weightDist (weightedSeededOutput (conditionalWeight p t) E)
        (seedFamilyWeight (fun _ : Seed => uniformWeight Out)) ≤
          firstWeight p t * ε + (K : ℝ) * μ t := by
    by_cases zero : firstWeight p t = 0
    · simpa only [zero, zero_mul, zero_add] using mul_nonneg threshold (nonnegative t)
    have positive : 0 < firstWeight p t := lt_of_le_of_ne (marginal.1 t) (Ne.symm zero)
    by_cases good : (K : ℝ) * μ t ≤ firstWeight p t
    · have conditionalCap : CappedWeight (conditionalWeight p t) K := by
        intro x
        apply (mul_le_mul_iff_right₀ positive).mp
        calc
          firstWeight p t * ((K : ℝ) * conditionalWeight p t x) =
              (K : ℝ) * p (t, x) := by
                rw [mul_left_comm, conditionalWeight_factor p probability.1]
          _ ≤ (K : ℝ) * μ t := mul_le_mul_of_nonneg_left (cap t x) threshold
          _ ≤ firstWeight p t * 1 := by simpa using good
      exact (mul_le_mul_of_nonneg_left (extract.dist_le (row t) conditionalCap)
        (marginal.1 t)).trans (le_add_of_nonneg_right (mul_nonneg threshold (nonnegative t)))
    · have at_most_one := weightDist_le_one ((row t).weightedSeededOutput E)
        (isProbabilityWeight_seedFamilyWeight (fun _ : Seed => uniformWeight Out)
          (fun _ => isProbabilityWeight_uniform Out))
      calc
        _ ≤ firstWeight p t * 1 := mul_le_mul_of_nonneg_left at_most_one (marginal.1 t)
        _ ≤ (K : ℝ) * μ t := by simpa using (le_of_lt (lt_of_not_ge good))
        _ ≤ firstWeight p t * ε + (K : ℝ) * μ t :=
          le_add_of_nonneg_left (mul_nonneg (marginal.1 t) error)
  have factor : p = fun tx : Tag × Source =>
      firstWeight p tx.1 * conditionalWeight p tx.1 tx.2 := by
    funext tx
    exact (conditionalWeight_factor p probability.1 tx.1 tx.2).symm
  have average := weightDist_tagged_seededOutput E (firstWeight p)
    (conditionalWeight p) marginal.1
  rw [← factor] at average
  rw [average]
  calc
    _ ≤ ∑ t, (firstWeight p t * ε + (K : ℝ) * μ t) :=
      Finset.sum_le_sum (fun t _ => row_bound t)
    _ = ε + (K : ℝ) * ∑ t, μ t := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, marginal.2, one_mul]

theorem weightedStrongSeededExtractor_leakage_average_dist_le {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : Source → Seed → Out} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : Tag × Source → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, p (t, x) ≤ μ t) :
    (∑ y, weightDist (mapWeight (fun tx => (tx.1, E tx.2 y)) p)
      (uniformExtensionWeight Out (firstWeight p))) / (Fintype.card Seed : ℝ) ≤
        ε + (K : ℝ) * ∑ t, μ t := by
  simpa only [weightDist_weightedSeededOutput_seedFamilyWeight] using
    weightedStrongSeededExtractor_leakage_dist_le extract error p probability μ nonnegative cap

end Algebraic.Cutwidth.Extractor.Internal
