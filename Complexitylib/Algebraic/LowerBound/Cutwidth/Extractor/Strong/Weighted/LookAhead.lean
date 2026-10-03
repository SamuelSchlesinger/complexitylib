/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Internal

/-!
# Tampered two-round look-ahead extraction

The actual calls are `s₁ = initialSeed q`, `r₁ = W x s₁`,
`s₂ = QExt q r₁`, and `r₂ = W x s₂`. The full left and right states
are independent given a transcript; each may contain arbitrarily
correlated honest and tampered inputs. The final law retains the entire
right state and both first outputs. These variables also determine both
initial seeds and both second seeds, including the tampered ones.

The intermediate honest seed guarantee follows from the first extraction;
it is not a hypothesis. The only seed hypothesis is the original joint
discrepancy of `initialSeed q` given the original transcript. Source bounds
are average joint envelopes, and all normalization assumptions are explicit.
No individual conditional row is required to satisfy an entropy bound.

This is the finite two-round, one-tampering argument of Chattopadhyay--Goyal--Li,
*Non-Malleable Extractors and Codes, with their Many Tampered Extensions*
(2015), Lemma 6.5 and Claim 6.6, printed pp.25--28:
<https://arxiv.org/pdf/1505.00107>. The stated error accounts explicitly for
both message alphabets and the original source envelopes. The paper's
nonuniform initial-seed bound and its longer-round induction are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The second seed and the complete retained left state have a normalized actual law. -/
theorem lookAheadSeedWeight_probability {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadSeedWeight w l r x q q' initialSeed W QExt) :=
  Internal.lookAheadSeedWeight_probability
    w l r x q q' initialSeed W QExt hw hl hr

/-- The final output and honest/tampered first outputs have a normalized actual law. -/
theorem lookAheadExtractionWeight_probability {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt) :=
  Internal.lookAheadExtractionWeight_probability
    w l r x x' q q' initialSeed W QExt hw hl hr

/-- The actual second seed is nearly uniform given all left variables and both initial seeds. -/
theorem WeightedStrongSeededExtractor.lookAhead_seed_dist_le
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadSeedWeight w l r x q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadSeedWeight w l r x q q' initialSeed W QExt)) ≤
        η + (ε + δ + (K : ℝ) * ∑ z, μ z) +
          (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z :=
  Internal.weightedStrongSeededExtractor_lookAhead_seed_dist_le
    first first_error second second_error w l r x q q' initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed

/-- The second left output is nearly uniform given the right state and both first outputs. -/
theorem WeightedStrongSeededExtractor.lookAhead_dist_le
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)) ≤
        2 * ε + η + δ + (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
          (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z :=
  Internal.weightedStrongSeededExtractor_lookAhead_dist_le
    first first_error second second_error w l r x x' q q' initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed

/-- A combined envelope budget bounds the complete two-round tampered output error. -/
theorem WeightedStrongSeededExtractor.lookAhead_dist_le_of_budget
    {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Nonempty Seed] [Nonempty Mid]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {K L : Nat} {ε η δ ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ)
    (budget : (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
      (L : ℝ) * Fintype.card (Seed × Seed) * (∑ z, ν z) ≤ ρ) :
    weightDist (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)
      (uniformSecondWeight (lookAheadExtractionWeight w l r x x' q q' initialSeed W QExt)) ≤
        2 * ε + η + δ + ρ :=
  Internal.weightedStrongSeededExtractor_lookAhead_dist_le_of_budget
    first first_error second second_error w l r x x' q q' initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed budget

end Algebraic.Cutwidth.Extractor
