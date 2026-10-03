/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Perturbation.Internal

/-!
# Robust extraction from an approximately independent uniform seed

The seed may be correlated with both the source and its retained tag. Its
distance from the law obtained by making that seed independently uniform
controls extraction with the actual tag and seed retained. An average joint
source-mass envelope suffices; no conditional source cap is assumed.

The actual-marginal bound charges the seed discrepancy twice. A comparison
with the reference law's retained marginal charges it once. This finite
stability deduction combines the existing leakage bound with deterministic
contraction and the triangle inequality. It supports alternating extraction
in the affine correlation-breaker argument of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1,
<https://arxiv.org/pdf/2110.12652>; the alternating program is a separate layer.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Approximate joint seed uniformity gives extraction retaining the actual tag/seed marginal. -/
theorem WeightedStrongSeededExtractor.perturbed_seed_dist_le
    {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    {E : Source → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : (Tag × Source) × Seed → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, firstWeight p (t, x) ≤ μ t)
    (seed : weightDist p (uniformSecondWeight p) ≤ δ) :
    weightDist (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2)) p)
      (uniformSecondWeight
        (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2)) p)) ≤
      ε + 2 * δ + (K : ℝ) * ∑ t, μ t :=
  Internal.weightedStrongSeededExtractor_perturbed_seed_dist_le
    extract error p probability μ nonnegative cap seed

/-- Comparing against the independent-seed reference marginal pays the seed discrepancy once. -/
theorem WeightedStrongSeededExtractor.perturbed_seed_reference_dist_le
    {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    {E : Source → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : (Tag × Source) × Seed → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, firstWeight p (t, x) ≤ μ t)
    (seed : weightDist p (uniformSecondWeight p) ≤ δ) :
    weightDist (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2)) p)
      (uniformSecondWeight
        (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2))
          (uniformSecondWeight p))) ≤ ε + δ + (K : ℝ) * ∑ t, μ t :=
  Internal.weightedStrongSeededExtractor_perturbed_seed_reference_dist_le
    extract error p probability μ nonnegative cap seed

end Algebraic.Cutwidth.Extractor
