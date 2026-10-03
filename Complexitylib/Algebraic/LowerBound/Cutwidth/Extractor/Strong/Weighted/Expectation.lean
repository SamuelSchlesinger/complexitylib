/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Expectation.Internal

/-!
# Bounded expectations and retained-seed statistical distance

For equal-mass real weights, every statistic valued in `[0,1]` changes by
at most total variation distance. Normalized strong extraction is also
equivalent to distance from the independent uniform seed-output law.

These elementary finite probability facts support the independence-merging
argument of Chattopadhyay and Liao, *Extractors for Sum of Two Sources*,
Lemma 3.26, p. 15: <https://arxiv.org/pdf/2110.12652>. That conditional
independence argument is a separate layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A statistic in `[0,1]` changes by at most the distance between equal-mass weights.
Neither normalization nor nonnegativity of the weights is needed. -/
theorem weightExpectation_sub_le_dist {α : Type*} [Fintype α]
    (p q f : α → ℝ) (mass : ∑ x, p x = ∑ x, q x)
    (lower : ∀ x, 0 ≤ f x) (upper : ∀ x, f x ≤ 1) :
    |(∑ x, p x * f x) - ∑ x, q x * f x| ≤ weightDist p q :=
  Internal.weightExpectation_sub_le_dist p q f mass lower upper

/-- Strong extraction bounds distance from the independent uniform retained-seed law. -/
theorem WeightedStrongSeededExtractor.dist_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    {E : α → Seed → Ω} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε)
    {p : α → ℝ} (probability : IsProbabilityWeight p) (cap : CappedWeight p K) :
    weightDist (weightedSeededOutput p E)
      (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) ≤ ε :=
  Internal.weightedStrongSeededExtractor_dist_le extract probability cap

/-- The finite-test and total-variation formulations of weighted strong extraction coincide. -/
theorem weightedStrongSeededExtractor_iff_dist_le {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω] [Nonempty Seed] [Nonempty Ω]
    (E : α → Seed → Ω) (K : Nat) (ε : ℝ) :
    WeightedStrongSeededExtractor E K ε ↔
      ∀ p : α → ℝ, IsProbabilityWeight p → CappedWeight p K →
        weightDist (weightedSeededOutput p E)
          (seedFamilyWeight (fun _ : Seed => uniformWeight Ω)) ≤ ε :=
  Internal.weightedStrongSeededExtractor_iff_dist_le E K ε

end Algebraic.Cutwidth.Extractor
