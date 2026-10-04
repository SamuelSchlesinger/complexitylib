/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal

/-!
# Alternating extraction retaining the entire opposite side

After a right-side observation, a seed computed from the left source and
that observation can extract from the right source. The actual output law
retains the full left state and the message, and pays for the seed discrepancy
once. The source budget is an average joint envelope, with no uniform bound
on individual conditional rows.

A second theorem supplies that seed using an actual affine extraction call.
Revealing its seed and extracted mask makes the first output a function of
the left side and transcript. The two checked extraction steps therefore
compose without resampling either source or imposing seed-mask independence.

These finite estimates support the alternating-extraction transitions in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1, printed pp.23--25:
<https://arxiv.org/pdf/2110.12652>. The advice correlation breaker's
flip-flop rounds use these transitions; its full tampering-set induction and
parameter budgets are `adviceCorrelationBreaker_dist_le`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual alternating output is a probability law when its original factors are normalized. -/
theorem alternatingExtractionWeight_probability {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (E : X → Seed → Out) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (alternatingExtractionWeight w l r v s x E) :=
  Internal.alternatingExtractionWeight_probability
    w l r v s x E hw hl hr

/-- A joint message-and-source envelope bounds extraction with the entire opposite side retained. -/
theorem WeightedStrongSeededExtractor.alternating_joint_dist_le
    {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype X]
    [Fintype Seed] [Fintype Out] [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (μ : Z × V → ℝ) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z))
    (nonnegative : ∀ zv, 0 ≤ μ zv)
    (cap : ∀ z v₀ x₀, w z * mapWeight (fun b => (v z b, x z b)) (r z) (v₀, x₀) ≤ μ (z, v₀))
    (seed : weightDist (alternatingSeedWeight w l r v s)
      (uniformSecondWeight (alternatingSeedWeight w l r v s)) ≤ δ) :
    weightDist (alternatingExtractionWeight w l r v s x E)
      (uniformSecondWeight (alternatingExtractionWeight w l r v s x E)) ≤
        ε + δ + (K : ℝ) * ∑ zv, μ zv :=
  Internal.weightedStrongSeededExtractor_alternating_joint_dist_le
    extract error w l r v s x μ hw hl hr nonnegative cap seed

/-- An alternating step pays only the observed message size against the original source envelope. -/
theorem WeightedStrongSeededExtractor.alternating_dist_le
    {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype X]
    [Fintype Seed] [Fintype Out] [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z))
    (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (r z) x₀ ≤ μ z)
    (seed : weightDist (alternatingSeedWeight w l r v s)
      (uniformSecondWeight (alternatingSeedWeight w l r v s)) ≤ δ) :
    weightDist (alternatingExtractionWeight w l r v s x E)
      (uniformSecondWeight (alternatingExtractionWeight w l r v s x E)) ≤
        ε + δ + (K : ℝ) * Fintype.card V * ∑ z, μ z :=
  Internal.weightedStrongSeededExtractor_alternating_dist_le
    extract error w l r v s x μ hw hl hr nonnegative cap seed

/-- Two actual extraction calls preserve normalization of the original joint law. -/
theorem affineAlternatingWeight_probability {Z A B X Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (source : Z → B → Y) (combine : X → X → X)
    (E : X → Seed → Mid) (F : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineAlternatingWeight w l r x mask y source combine E F) :=
  Internal.affineAlternatingWeight_probability
    w l r x mask y source combine E F hw hl hr

/-- An affine extraction seeds the next right extraction while retaining the whole left state. -/
theorem WeightedStrongSeededExtractor.affine_alternating_dist_le
    {Z A B X Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed]
    [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {E : X → Seed → Mid} {F : Y → Mid → Out} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor E K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor F L η) (second_error : 0 ≤ η)
    (combine : X → X → X) (translate : Mid → Mid ≃ Mid)
    (linear : ∀ a b s, E (combine a b) s = translate (E b s) (E a s))
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (source : Z → B → Y) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (source z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    weightDist (affineAlternatingWeight w l r x mask y source combine E F)
      (uniformSecondWeight (affineAlternatingWeight w l r x mask y source combine E F)) ≤
        η + (ε + δ + (K : ℝ) * ∑ z, μ z) +
          (L : ℝ) * Fintype.card (Seed × Mid) * ∑ z, ν z :=
  Internal.weightedStrongSeededExtractor_affine_alternating_dist_le
    first first_error second second_error combine translate linear
    w l r x mask y source μ ν hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed

end Algebraic.Cutwidth.Extractor
