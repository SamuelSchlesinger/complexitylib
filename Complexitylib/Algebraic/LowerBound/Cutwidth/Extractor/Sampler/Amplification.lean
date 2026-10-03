/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Internal

/-!
# Amplifying a finite sampler by neighbor coverage

A large set of outer seeds reaches more base seeds than a good input can send
into a test set. Therefore few outer seeds have every candidate in that test.
The bad-input inclusion preserves the sampler's arbitrary source weights and
its failure probability.

This is the finite reduction in Chattopadhyay and Liao,
*Extractors for Sum of Two Sources* (2021), Appendix A, proof of Lemma 3.17:
https://arxiv.org/abs/2110.12652. Seeded extraction also gives the needed
coverage by testing the full neighbor image. This permits a constant-error
extractor to supply the neighbor map when its seed count is affordable.

The theorems prove these implications. An explicit neighbor map with the
required parameters and a uniform polynomial-time evaluator remains a separate
construction obligation.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- At a base-good input, fewer than `K` outer seeds have all candidates in the
test set. The strict coverage gap remains strict because the base is nonempty. -/
theorem NeighborCoverage.card_allHitSeeds_lt {α Outer Candidate Base Ω : Type*}
    [Fintype Outer] [Fintype Candidate] [Fintype Base] [Nonempty Base]
    {Γ : Outer → Candidate → Base} {K : Nat} {ρ ε₀ : ℝ}
    (cover : NeighborCoverage Γ K ρ) (separate : 2 * ε₀ < ρ)
    (E : α → Base → Ω) (T : Finset Ω) (x : α)
    (good : (seedHits E T x : ℝ) ≤ 2 * ε₀ * Fintype.card Base) :
    (allHitSeeds (fun x y z => E x (Γ y z)) T x).card < K :=
  Internal.card_allHitSeeds_lt cover separate E T x good

/-- Extraction forces every large support to reach at least a `1 - ε` fraction
of outputs. The source support and the uniform seed are nonempty. -/
theorem FlatSeededExtractor.neighborCoverage {Outer Candidate Base : Type*}
    [Fintype Candidate] [Nonempty Candidate] [Fintype Base]
    {Γ : Outer → Candidate → Base} {K : Nat} {ε : ℝ}
    (extract : FlatSeededExtractor Γ K ε) (positive : 0 < K) :
    NeighborCoverage Γ K (1 - ε) :=
  Internal.neighborCoverage_of_flatSeededExtractor extract positive

/-- Compose a sampler with a covering neighbor map. The target tests may be
smaller, and the source point-mass and failure bounds are preserved exactly. -/
theorem Sampler.amplify {α Outer Candidate Base Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Candidate] [Fintype Base] [Fintype Ω]
    [Nonempty Base] {E : α → Base → Ω} {Γ : Outer → Candidate → Base}
    {K : Nat} {L ε₀ ε δ ρ : ℝ}
    (sample : Sampler E L ε₀ δ) (cover : NeighborCoverage Γ K ρ)
    (small : ε ≤ ε₀) (separate : 2 * ε₀ < ρ)
    (budget : (K : ℝ) ≤ 2 * ε * Fintype.card Outer) :
    SomewhereSampler (fun x y z => E x (Γ y z)) L ε δ :=
  Internal.sampler_amplify sample cover small separate budget

/-- Listing every base seed gives full coverage of every nonempty support. -/
theorem neighborCoverage_seedProjection {Outer Base : Type*} [Fintype Base]
    {K : Nat} (positive : 0 < K) :
    NeighborCoverage (fun (_ : Outer) (z : Base) => z) K 1 :=
  Internal.neighborCoverage_seedProjection positive

/-- Listing every output at each outer seed has zero failure probability for
every proper-density test. This example uses as many candidates as outputs. -/
theorem somewhereSampler_seedProjection {α Outer Ω : Type*}
    [Fintype α] [Fintype Outer] [Fintype Ω] [Nonempty Ω]
    {L ε : ℝ} (nonneg : 0 ≤ ε) (small : ε < 1) :
    SomewhereSampler (fun (_ : α) (_ : Outer) (z : Ω) => z) L ε 0 :=
  Internal.somewhereSampler_seedProjection nonneg small

end Algebraic.Cutwidth.Extractor
