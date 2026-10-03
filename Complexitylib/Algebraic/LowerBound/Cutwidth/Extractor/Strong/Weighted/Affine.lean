/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Internal

/-!
# The first extraction step on a source with a correlated mask

The source and complete right state are independent given a transcript.
The seed may be correlated with all other right-side values. An average
joint-mass envelope and the seed's joint discrepancy suffice for extraction
retaining the entire right state. If combining with a fixed right mask acts
as a bijection on the extractor output, the same error bound holds on the
combined input. Addition and pointwise XOR provide these bijections for
linear extractors.

This supplies the retained-law estimate for the affine initial-extraction
step in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, proof of Theorem 6.1, printed p.23:
<https://arxiv.org/pdf/2110.12652>. The actual program specialization is
provided separately. Matching the paper's parameters and transcript budgets,
the subsequent correlation-breaker call, and evolving alternating-extraction
invariants require further work.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual retained extraction law is normalized when its three factor laws are normalized. -/
theorem retainedExtractionWeight_probability {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (E : X → Seed → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (retainedExtractionWeight w l r x y E) :=
  Internal.retainedExtractionWeight_probability w l r x y E hw hl hr

/-- Extraction retaining the whole right state pays only for its observed seed discrepancy. -/
theorem WeightedStrongSeededExtractor.retained_dist_le {Z A B X Seed Out : Type*}
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
        ε + δ + (K : ℝ) * ∑ z, μ z :=
  Internal.weightedStrongSeededExtractor_retained_dist_le
    extract error w l r x y μ hw hl hr nonnegative cap seed

/-- Combining the input with a right mask is exactly a retained-tag output bijection. -/
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
          (retainedExtractionWeight w l r x y E) :=
  Internal.affineExtractionWeight_eq_map w l r x mask y combine E translate linear

/-- The actual masked-input extraction law preserves probability. -/
theorem affineExtractionWeight_probability {Z A B X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (combine : X → X → X) (E : X → Seed → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineExtractionWeight w l r x mask y combine E) :=
  Internal.affineExtractionWeight_probability w l r x mask y combine E hw hl hr

/-- A right-side mask commuting with extraction through output bijections adds no error. -/
theorem WeightedStrongSeededExtractor.affine_dist_le {Z A B X Seed Out : Type*}
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
        ε + δ + (K : ℝ) * ∑ z, μ z :=
  Internal.weightedStrongSeededExtractor_affine_dist_le extract error combine translate linear
    w l r x mask y μ hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor
