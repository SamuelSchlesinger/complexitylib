/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Seed

/-!
# Two-sided merging from a conditionally smooth uniform source

The honest source is close to uniform jointly with the transcript and a
selected original left observation. A coupling repairs only that honest
coordinate while preserving the complete original left state. Observing
the actual original prefix then pays its alphabet size divided by the
source alphabet size. Extraction keeps the full right state, selected
left observation, prefix, and additional left leak. The repair costs the
original distance once because this entire retained marginal is unchanged.

This is a finite weighted consumer for the smooth-source step in
Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Theorem 6.1,
printed pp.22--25, using their Lemma 3.26:
<https://arxiv.org/abs/2110.12652>. The coordinate repair and its exact
retained-marginal accounting are formalized here; the full affine
correlation-breaker construction is a separate layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual retained seed law is normalized whenever the original factors are normalized. -/
theorem smoothMergingSeedWeight_probability {Z A B U Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothMergingSeedWeight w l r u q v y) :=
  Internal.smoothMergingSeedWeight_probability w l r u q v y hw hl hr

/-- The output law keeps the actual original right state and all stated left observations. -/
theorem smoothTwoSidedExtractionWeight_probability {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Q]
    [Fintype W] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W) (E : X → Seed → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothTwoSidedExtractionWeight w l r x u q v y leak E) :=
  Internal.smoothTwoSidedExtractionWeight_probability w l r x u q v y leak E hw hl hr

/-- Smooth uniformity before an actual prefix suffices; no conditional source cap is assumed. -/
theorem WeightedStrongSeededExtractor.smooth_two_sided_dist_le
    {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype W] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (observedSeedWeight w l u x)
      (uniformSecondWeight (observedSeedWeight w l u x)) ≤ ρ)
    (seed : weightDist (smoothMergingSeedWeight w l r u q v y)
      (uniformSecondWeight (smoothMergingSeedWeight w l r u q v y)) ≤ δ) :
    weightDist (smoothTwoSidedExtractionWeight w l r x u q v y leak E)
      (uniformSecondWeight (smoothTwoSidedExtractionWeight w l r x u q v y leak E)) ≤
        ε + δ + ρ + (K : ℝ) * Fintype.card W * Fintype.card Q / Fintype.card X :=
  Internal.weightedStrongSeededExtractor_smooth_two_sided_dist_le extract error
    w l r x u q v y leak hw hl hr source seed

/-- Extra original left observations do not change the averaged error of a prefix-only seed. -/
theorem smoothMergingSeedWeight_prefix_dist {Z A B U Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (u : Z → A → U) (q : Z → A → Q)
    (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z, IsProbabilityWeight (l z)) :
    weightDist (smoothMergingSeedWeight w l r u q
      (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)))
      (uniformSecondWeight (smoothMergingSeedWeight w l r u q
        (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)))) =
      weightDist (observedSeedWeight (observedTranscriptWeight w l q)
        (fun zq => r zq.1) v y)
        (uniformSecondWeight (observedSeedWeight (observedTranscriptWeight w l q)
          (fun zq => r zq.1) v y)) :=
  Internal.smoothMergingSeedWeight_prefix_dist w l r u q v y hw hl

/-- The seed need only be close to uniform with its actual prefix and right observation. -/
theorem WeightedStrongSeededExtractor.smooth_two_sided_dist_le_of_prefix_seed
    {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype W] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (observedSeedWeight w l u x)
      (uniformSecondWeight (observedSeedWeight w l u x)) ≤ ρ)
    (seed : weightDist (observedSeedWeight (observedTranscriptWeight w l q)
      (fun zq => r zq.1) v y)
      (uniformSecondWeight (observedSeedWeight (observedTranscriptWeight w l q)
        (fun zq => r zq.1) v y)) ≤ δ) :
    weightDist (smoothTwoSidedExtractionWeight w l r x u q
      (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)) leak E)
      (uniformSecondWeight (smoothTwoSidedExtractionWeight w l r x u q
        (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)) leak E)) ≤
        ε + δ + ρ + (K : ℝ) * Fintype.card W * Fintype.card Q / Fintype.card X :=
  Internal.weightedStrongSeededExtractor_smooth_two_sided_dist_le_of_prefix_seed extract error
    w l r x u q v y leak hw hl hr source seed

end Algebraic.Cutwidth.Extractor
