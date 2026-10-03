/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript

/-!
# Extraction with an arbitrary correlated right state

Specializing two-sided leakage to trivial observations keeps the entire
right variable without paying for its alphabet. Projecting away the trivial
tags preserves the actual retained marginal. Only the seed's joint distance
given the original transcript is charged.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem retainedSeedWeight_observed {Z B Seed : Type*} [Fintype Z] [Fintype B]
    [Fintype Seed] (w : Z → ℝ) (r : Z → B → ℝ) (y : Z → B → Seed) :
    observedSeedWeight w r (fun _ _ => ()) y =
      mapWeight (fun zy : Z × Seed => ((zy.1, ()), zy.2)) (retainedSeedWeight w r y) := by
  unfold retainedSeedWeight observedSeedWeight
  rw [mapWeight_comp]

theorem retainedExtractionWeight_project {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (E : X → Seed → Out) :
    mapWeight (fun p : ((Z × B) × (Unit × Unit)) × Out => (p.1.1, p.2))
      (twoSidedExtractionWeight w l r x y (fun _ _ => ()) (fun _ _ => ())
        (fun _ _ _ => ()) E) = retainedExtractionWeight w l r x y E := by
  rw [twoSidedExtractionWeight_eq_map, mapWeight_comp]
  rfl

theorem retainedExtractionWeight_probability {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (E : X → Seed → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (retainedExtractionWeight w l r x y E) := by
  rw [← retainedExtractionWeight_project]
  exact (twoSidedExtractionWeight_probability w l r x y (fun _ _ => ())
    (fun _ _ => ()) (fun _ _ _ => ()) E hw hl hr).map (fun p => (p.1.1, p.2))

theorem weightedStrongSeededExtractor_retained_dist_le {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out] {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    weightDist (retainedExtractionWeight w l r x y E)
      (uniformSecondWeight (retainedExtractionWeight w l r x y E)) ≤
        ε + δ + (K : ℝ) * ∑ z, μ z := by
  classical
  have observed : weightDist (observedSeedWeight w r (fun _ _ => ()) y)
      (uniformSecondWeight (observedSeedWeight w r (fun _ _ => ()) y)) ≤ δ := by
    rw [retainedSeedWeight_observed]
    exact (weightDist_uniformSecond_map_first_le (retainedSeedWeight w r y)
      (fun z => (z, ()))).trans seed
  have jointCap (z : Z) (u₀ : Unit) (x₀ : X) :
      w z * mapWeight (fun a => (((), x z a) : Unit × X)) (l z) (u₀, x₀) ≤ μ z := by
    cases u₀
    simpa [mapWeight, Prod.mk.injEq] using cap z x₀
  have bound := extract.two_sided_leakage_dist_le error w l r x y
    (fun _ _ => ()) (fun _ _ => ()) (fun _ _ _ => ()) (fun zu : Z × Unit => μ zu.1)
    hw hl hr (fun zu => nonnegative zu.1) jointCap observed
  have project := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight w l r x y (fun _ _ => ()) (fun _ _ => ())
      (fun _ _ _ => ()) E) (fun p => p.1)
  rw [retainedExtractionWeight_project] at project
  exact project.trans (by simpa [Fintype.sum_prod_type] using bound)

theorem affineExtractionWeight_eq_map {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (combine : X → X → X) (E : X → Seed → Out)
    (translate : X → Seed → Out ≃ Out)
    (linear : ∀ a b s, E (combine a b) s = translate b s (E a s)) :
    affineExtractionWeight w l r x mask y combine E =
      mapWeight (fun p : (Z × B) × Out =>
        (p.1, translate (mask p.1.1 p.1.2) (y p.1.1 p.1.2) p.2))
          (retainedExtractionWeight w l r x y E) := by
  unfold affineExtractionWeight retainedExtractionWeight
  rw [mapWeight_comp]
  simp only [linear]

theorem affineExtractionWeight_probability {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (combine : X → X → X) (E : X → Seed → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineExtractionWeight w l r x mask y combine E) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem weightedStrongSeededExtractor_affine_dist_le {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out] {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (combine : X → X → X) (translate : X → Seed → Out ≃ Out)
    (linear : ∀ a b s, E (combine a b) s = translate b s (E a s))
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    weightDist (affineExtractionWeight w l r x mask y combine E)
      (uniformSecondWeight (affineExtractionWeight w l r x mask y combine E)) ≤
        ε + δ + (K : ℝ) * ∑ z, μ z := by
  rw [affineExtractionWeight_eq_map w l r x mask y combine E translate linear]
  rw [weightDist_uniformSecond_fiberEquiv (retainedExtractionWeight w l r x y E)
    (fun zb => translate (mask zb.1 zb.2) (y zb.1 zb.2))]
  exact weightedStrongSeededExtractor_retained_dist_le
    extract error w l r x y μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor.Internal
