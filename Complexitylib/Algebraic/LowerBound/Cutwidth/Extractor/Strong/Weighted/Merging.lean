/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic

/-!
# Strong extraction with two-sided finite leakage

A shared transcript indexes independent left and right distributions. A
joint source-mass envelope controls the left observation. The seed is close
to uniform given the right observation. An additional finite leak may depend
on both the left variable and that right observation. Extraction retains the
entire right variable and both left leaks; its error is the extractor error,
the seed discrepancy, and the envelope total times the leak's alphabet size.

The bound permits arbitrary low-entropy transcript fibers. It is the finite
weighted form underlying the independence-merging lemma in
Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Lemma 3.26
(printed p.15), used in Theorem 6.1 (pp.22--25):
<https://arxiv.org/abs/2110.12652>. That lemma credits Chattopadhyay--Goodman--Liao
and ideas of Chattopadhyay--Li. No correlation-breaker algorithm is assumed
or constructed in this probability layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The retained extraction law is the actual deterministic image of the factored source. -/
theorem twoSidedExtractionWeight_eq_map {Z A B X Seed Out U V W : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (E : X → Seed → Out) :
    twoSidedExtractionWeight w l r x y u v leak E =
      mapWeight (fun p : (Z × B) × A =>
        ((p.1, (u p.1.1 p.2, leak p.1.1 (v p.1.1 p.1.2) p.2)),
          E (x p.1.1 p.2) (y p.1.1 p.1.2))) (factoredWeight w l r) :=
  Internal.twoSidedExtractionWeight_eq_map w l r x y u v leak E

/-- Normalized factored sources give a normalized retained extraction law. -/
theorem twoSidedExtractionWeight_probability {Z A B X Seed Out U V W : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Out] [Fintype U] [Fintype W]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (E : X → Seed → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (twoSidedExtractionWeight w l r x y u v leak E) :=
  Internal.twoSidedExtractionWeight_probability w l r x y u v leak E hw hl hr

/-- A joint-mass envelope pays for finite leakage without a cap on each conditional source. -/
theorem WeightedStrongSeededExtractor.two_sided_leakage_dist_le
    {Z A B X Seed Out U V W : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed] [Fintype Out]
    [Fintype U] [Fintype V] [Fintype W] [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (μ : Z × U → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ z u₀ x₀,
      w z * mapWeight (fun a => (u z a, x z a)) (l z) (u₀, x₀) ≤ μ (z, u₀))
    (seed : weightDist (observedSeedWeight w r v y)
      (uniformSecondWeight (observedSeedWeight w r v y)) ≤ δ) :
    weightDist (twoSidedExtractionWeight w l r x y u v leak E)
      (uniformSecondWeight (twoSidedExtractionWeight w l r x y u v leak E)) ≤
        ε + δ + (K : ℝ) * Fintype.card W * ∑ t, μ t :=
  Internal.weightedStrongSeededExtractor_two_sided_leakage_dist_le extract error
    w l r x y u v leak μ hw hl hr nonnegative cap seed

/-- A budget on the average joint envelope gives an additive leakage error. -/
theorem WeightedStrongSeededExtractor.two_sided_leakage_dist_le_of_budget
    {Z A B X Seed Out U V W : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed] [Fintype Out]
    [Fintype U] [Fintype V] [Fintype W] [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (μ : Z × U → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ z u₀ x₀,
      w z * mapWeight (fun a => (u z a, x z a)) (l z) (u₀, x₀) ≤ μ (z, u₀))
    (seed : weightDist (observedSeedWeight w r v y)
      (uniformSecondWeight (observedSeedWeight w r v y)) ≤ δ)
    (budget : (K : ℝ) * Fintype.card W * ∑ t, μ t ≤ ρ) :
    weightDist (twoSidedExtractionWeight w l r x y u v leak E)
      (uniformSecondWeight (twoSidedExtractionWeight w l r x y u v leak E)) ≤
        ε + δ + ρ :=
  Internal.weightedStrongSeededExtractor_two_sided_leakage_dist_le_of_budget extract error
    w l r x y u v leak μ hw hl hr nonnegative cap seed budget

end Algebraic.Cutwidth.Extractor
