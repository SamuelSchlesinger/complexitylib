/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Internal

/-!
# Strong extraction for arbitrary finite probability weights

For positive thresholds, the flat and weighted strong-extractor contracts
are equivalent. Decomposing a capped source into exact-size flat sources
and averaging their test bounds introduces no extra statistical error.
The converse identifies the uniform law on every finite support with its
weights on the ambient type. This allows the checked flat-source extractor
to be used on nonuniform conditional distributions.

The mixture decomposition is a finite existence argument, supplied by
`Strong.FlatMixture` using Mathlib's Birkhoff--von Neumann theorem. It makes
no claim about computing a decomposition of arbitrary real probabilities.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Uniform weights on a nonempty finite support are normalized. -/
theorem isProbabilityWeight_flatWeight {α : Type*} [Fintype α]
    (P : Finset α) (nonempty : P.Nonempty) : IsProbabilityWeight (flatWeight P) :=
  Internal.probabilityWeight_flatWeight P nonempty

/-- A uniform support satisfies every cap whose threshold is at most its size. -/
theorem cappedWeight_flatWeight {α : Type*} (P : Finset α) {K : Nat}
    (size : K ≤ P.card) : CappedWeight (flatWeight P) K :=
  Internal.cappedWeight_flatWeight P size

/-- Uniform weights recover the existing finite seeded-test probability. -/
theorem weightedSeededTestProb_uniformWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (E : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    weightedSeededTestProb (uniformWeight α) E T = seededTestProb E T :=
  Internal.weightedSeededTestProb_uniformWeight E T

/-- Sampling uniformly on a finite support agrees with the corresponding weights. -/
theorem weightedSeededTestProb_flatWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] (E : α → Seed → Ω) (P : Finset α)
    (T : Finset (Seed × Ω)) :
    weightedSeededTestProb (flatWeight P) E T = seededTestProb (fun x : P => E x.val) T :=
  Internal.weightedSeededTestProb_flatWeight E P T

/-- Seeded-test probability is linear in the source weights. -/
theorem weightedSeededTestProb_mixture {α ι Seed Ω : Type*}
    [Fintype α] [Fintype ι] [Fintype Seed]
    (w : ι → ℝ) (p : ι → α → ℝ) (E : α → Seed → Ω) (T : Finset (Seed × Ω)) :
    weightedSeededTestProb (fun x => ∑ i, w i * p i x) E T =
      ∑ i, w i * weightedSeededTestProb (p i) E T :=
  Internal.weightedSeededTestProb_mixture w p E T

/-- Flat strong extraction extends to all capped finite sources with the same error. -/
theorem FlatStrongSeededExtractor.weightedStrongSeededExtractor {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : FlatStrongSeededExtractor E K ε) (positive : 0 < K) :
    WeightedStrongSeededExtractor E K ε :=
  Internal.weightedStrong_of_flat extract positive

/-- A weighted strong-extractor guarantee includes every nonempty flat source. -/
theorem WeightedStrongSeededExtractor.flatStrongSeededExtractor {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) : FlatStrongSeededExtractor E K ε :=
  Internal.flatStrong_of_weighted extract

/-- At positive thresholds, the weighted and flat strong contracts are equivalent. -/
theorem weightedStrongSeededExtractor_iff_flat {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (positive : 0 < K) :
    WeightedStrongSeededExtractor E K ε ↔ FlatStrongSeededExtractor E K ε :=
  ⟨WeightedStrongSeededExtractor.flatStrongSeededExtractor,
    fun h => h.weightedStrongSeededExtractor positive⟩

end Algebraic.Cutwidth.Extractor
