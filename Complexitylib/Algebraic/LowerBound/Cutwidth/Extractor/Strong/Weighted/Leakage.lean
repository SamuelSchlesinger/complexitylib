/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Leakage.Internal

/-!
# Strong extraction with an average leakage budget

A joint point-mass envelope `p (tag, x) ≤ μ tag` suffices for extraction
retaining both the entire tag and the independent uniform seed. The error
is at most the extractor error plus `K * ∑ tag, μ tag`. No bound on each
normalized conditional row is assumed; zero-mass rows contribute zero.

This finite row estimate supplies the average conditional-entropy step used
in Chattopadhyay and Liao, *Extractors for Sum of Two Sources*, Lemma 3.26,
p. 15: <https://arxiv.org/pdf/2110.12652>. The independence-merging argument
and the affine correlation-breaker applications in Chattopadhyay, Goodman,
and Liao, <https://eccc.weizmann.ac.il/report/2021/075/>, are separate layers.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A joint row envelope gives extraction retaining the full leakage tag and uniform seed. -/
theorem WeightedStrongSeededExtractor.leakage_dist_le {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : Source → Seed → Out} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : Tag × Source → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, p (t, x) ≤ μ t) :
    weightDist (weightedSeededOutput p (fun tx y => (tx.1, E tx.2 y)))
      (seedFamilyWeight (fun _ : Seed => uniformExtensionWeight Out (firstWeight p))) ≤
        ε + (K : ℝ) * ∑ t, μ t :=
  Internal.weightedStrongSeededExtractor_leakage_dist_le
    extract error p probability μ nonnegative cap

/-- The same leakage guarantee as the average distance over the independent uniform seed. -/
theorem WeightedStrongSeededExtractor.leakage_average_dist_le {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : Source → Seed → Out} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : Tag × Source → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, p (t, x) ≤ μ t) :
    (∑ y, weightDist (mapWeight (fun tx => (tx.1, E tx.2 y)) p)
      (uniformExtensionWeight Out (firstWeight p))) / (Fintype.card Seed : ℝ) ≤
        ε + (K : ℝ) * ∑ t, μ t :=
  Internal.weightedStrongSeededExtractor_leakage_average_dist_le
    extract error p probability μ nonnegative cap

end Algebraic.Cutwidth.Extractor
