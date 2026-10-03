/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Independence.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Independence.Internal

/-!
# Finite independence merging for overlapping tampering sets

Source copies indexed by `T` enter a joint point-mass envelope. The actual
seed is close to uniform given the transcript and seed copies indexed by
`S`. Extraction then remains close to uniform given the transcript, every
seed, and all tampered outputs in `S ∪ T`. The sets need not be disjoint.

The exact leakage cost is `K * |Out| ^ |S| * ∑ μ`. Bounding that cost by
the extractor error gives `2 * ε + δ`. This is the finite envelope form of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Lemma 3.26, p.15,
<https://arxiv.org/pdf/2110.12652>. That source credits Chattopadhyay--Goodman--Liao
and ideas of Chattopadhyay--Li. Here conditional independence is expressed by
explicit normalized factored laws; no logarithmic entropy definition or
correlation-breaker construction is introduced.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Merge source-side and seed-side independence, retaining every seed and the selected outputs. -/
theorem WeightedStrongSeededExtractor.independence_merging_dist_le
    {Z X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype X] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → (X × (Fin t → X)) → ℝ)
    (r : Z → (Seed × (Fin t → Seed)) → ℝ) (S T : Finset (Fin t))
    (μ : Z × (T → X) → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ zu, 0 ≤ μ zu)
    (cap : ∀ z u x,
      w z * mapWeight (fun a => ((fun j : T => a.2 j), a.1)) (l z) (u, x) ≤ μ (z, u))
    (seed : weightDist
      (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))
      (uniformSecondWeight
        (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))) ≤ δ) :
    weightDist (independenceMergingWeight w l r E S T)
      (uniformSecondWeight (independenceMergingWeight w l r E S T)) ≤
        ε + δ + (K : ℝ) * (Fintype.card Out : ℝ) ^ S.card * ∑ zu, μ zu :=
  Internal.weightedStrongSeededExtractor_independence_merging_dist_le extract error
    w l r S T μ hw hl hr nonnegative cap seed

/-- Paying at most one extractor error for leakage gives the `2ε + δ` merging bound. -/
theorem WeightedStrongSeededExtractor.independence_merging_dist_le_of_budget
    {Z X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype X] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → (X × (Fin t → X)) → ℝ)
    (r : Z → (Seed × (Fin t → Seed)) → ℝ) (S T : Finset (Fin t))
    (μ : Z × (T → X) → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ zu, 0 ≤ μ zu)
    (cap : ∀ z u x,
      w z * mapWeight (fun a => ((fun j : T => a.2 j), a.1)) (l z) (u, x) ≤ μ (z, u))
    (seed : weightDist
      (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))
      (uniformSecondWeight
        (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))) ≤ δ)
    (budget : (K : ℝ) * (Fintype.card Out : ℝ) ^ S.card * ∑ zu, μ zu ≤ ε) :
    weightDist (independenceMergingWeight w l r E S T)
      (uniformSecondWeight (independenceMergingWeight w l r E S T)) ≤ 2 * ε + δ :=
  Internal.weightedStrongSeededExtractor_independence_merging_dist_le_of_budget extract error
    w l r S T μ hw hl hr nonnegative cap seed budget

end Algebraic.Cutwidth.Extractor
