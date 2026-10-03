/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Ring

/-!
# Exact distance averages for two-sided extraction

The actual joint distance and its uniform-seed counterpart are expectations
of the same statistic in `[0,1]`. The entire right variable remains in the
actual output tag. Independence conditioned on the transcript makes its
additional values irrelevant to each fixed left-row distance.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem merging_uniform_expectation {ι Seed : Type*} [Fintype ι] [Fintype Seed]
    (p : ι × Seed → ℝ) (f : ι × Seed → ℝ) :
    ∑ iy, uniformSecondWeight p iy * f iy =
      (∑ y, ∑ i, firstWeight p i * f (i, y)) / (Fintype.card Seed : ℝ) := by
  simp only [Fintype.sum_prod_type, uniformSecondWeight, uniformExtensionWeight,
    uniformWeight, div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem merging_seeded_nested_dist {ι Tag X Seed Out : Type*}
    [Fintype ι] [Fintype Tag] [Fintype X] [Fintype Seed] [Fintype Out]
    (w : ι → ℝ) (p : ι → Tag × X → ℝ) (E : X → Seed → Out)
    (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist
      (weightedSeededOutput
        (fun tx : (ι × Tag) × X => w tx.1.1 * p tx.1.1 (tx.1.2, tx.2))
        (fun tx y => (tx.1, E tx.2 y)))
      (seedFamilyWeight (fun _ : Seed => uniformExtensionWeight Out
        (firstWeight (fun tx : (ι × Tag) × X => w tx.1.1 * p tx.1.1 (tx.1.2, tx.2))))) =
      (∑ y, ∑ i, w i *
        weightDist (mapWeight (fun tx : Tag × X => (tx.1, E tx.2 y)) (p i))
          (uniformSecondWeight
            (mapWeight (fun tx : Tag × X => (tx.1, E tx.2 y)) (p i)))) /
              (Fintype.card Seed : ℝ) := by
  rw [weightDist_weightedSeededOutput_seedFamilyWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  have first := firstWeight_map_fiber
    (fun tx : (ι × Tag) × X => w tx.1.1 * p tx.1.1 (tx.1.2, tx.2))
    (fun _ a => E a y)
  have uniform : uniformExtensionWeight Out
      (firstWeight (fun tx : (ι × Tag) × X => w tx.1.1 * p tx.1.1 (tx.1.2, tx.2))) =
      uniformSecondWeight (mapWeight (fun tx => (tx.1, E tx.2 y))
        (fun tx : (ι × Tag) × X => w tx.1.1 * p tx.1.1 (tx.1.2, tx.2))) := by
    simp only [uniformSecondWeight, first]
  rw [uniform, merging_map_nested w p (fun _ a => E a y)]
  exact weightDist_uniformSecond_tagged w
    (fun i => mapWeight (fun tx : Tag × X => (tx.1, E tx.2 y)) (p i)) nonnegative

variable {Z A B X Seed Out U V W : Type*}
variable [Fintype Z] [Fintype A] [Fintype B] [Fintype X]
variable [Fintype Seed] [Fintype Out] [Fintype U] [Fintype V] [Fintype W]

omit [Fintype Z] [Fintype Seed] [Fintype V] in
theorem mergingDistance_range [Nonempty Out] (l : Z → A → ℝ) (x : Z → A → X)
    (u : Z → A → U) (leak : Z → V → A → W) (E : X → Seed → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) (p : (Z × V) × Seed) :
    0 ≤ mergingDistance l x u leak E p ∧ mergingDistance l x u leak E p ≤ 1 := by
  have probability := mergingOutputWeight_probability _ E
    (mergingLeftWeight_probability l x u leak hl p.1) p.2
  exact ⟨weightDist_nonneg _ _, weightDist_le_one probability probability.uniformSecond⟩

theorem twoSidedExtractionWeight_dist_eq (w : Z → ℝ) (l : Z → A → ℝ)
    (r : Z → B → ℝ) (x : Z → A → X) (y : Z → B → Seed)
    (u : Z → A → U) (v : Z → B → V) (leak : Z → V → A → W)
    (E : X → Seed → Out) (hw : IsProbabilityWeight w)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (twoSidedExtractionWeight w l r x y u v leak E)
      (uniformSecondWeight (twoSidedExtractionWeight w l r x y u v leak E)) =
        ∑ p, observedSeedWeight w r v y p * mergingDistance l x u leak E p := by
  have tagged := weightDist_uniformSecond_tagged
    (fun zb : Z × B => w zb.1 * r zb.1 zb.2)
    (fun zb => mergingOutputWeight (mergingLeftWeight l x u leak (zb.1, v zb.1 zb.2))
      E (y zb.1 zb.2))
    (fun zb => mul_nonneg (hw.1 _) ((hr _).1 _))
  have actual : weightDist (twoSidedExtractionWeight w l r x y u v leak E)
      (uniformSecondWeight (twoSidedExtractionWeight w l r x y u v leak E)) =
        ∑ zb : Z × B, (w zb.1 * r zb.1 zb.2) *
          mergingDistance l x u leak E ((zb.1, v zb.1 zb.2), y zb.1 zb.2) := by
    unfold twoSidedExtractionWeight
    simpa only [mergingDistance, mergingOutputWeight_left]
      using tagged
  rw [actual]
  exact (merging_sum_mapWeight_mul _ _ (mergingDistance l x u leak E)).symm

theorem leakageSourceWeight_dist_eq (w : Z → ℝ) (l : Z → A → ℝ)
    (r : Z → B → ℝ) (x : Z → A → X) (y : Z → B → Seed)
    (u : Z → A → U) (v : Z → B → V) (leak : Z → V → A → W)
    (E : X → Seed → Out) (hw : IsProbabilityWeight w)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist
      (weightedSeededOutput (leakageSourceWeight w l r x u v leak)
        (fun tx seed => (tx.1, E tx.2 seed)))
      (seedFamilyWeight (fun _ : Seed => uniformExtensionWeight Out
        (firstWeight (leakageSourceWeight w l r x u v leak)))) =
      ∑ p, uniformSecondWeight (observedSeedWeight w r v y) p *
        mergingDistance l x u leak E p := by
  rw [merging_uniform_expectation, observedSeedWeight_first]
  unfold leakageSourceWeight
  simpa only [mergingDistance, mergingOutputWeight, mergingLeftWeight] using
    merging_seeded_nested_dist
      (fun zv : Z × V => w zv.1 * mapWeight (v zv.1) (r zv.1) zv.2)
      (mergingLeftWeight l x u leak) E
      (fun zv => mul_nonneg (hw.1 _) (((hr _).map (v _)).1 _))

end Algebraic.Cutwidth.Extractor.Internal
