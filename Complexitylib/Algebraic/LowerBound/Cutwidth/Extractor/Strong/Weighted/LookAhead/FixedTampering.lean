/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Internal.Basic

/-!
# A refresh with an arbitrary left-only tampered seed

The honest refresh rereads the original right source, seeded by the actual
first left extraction. The tampered refresh uses an arbitrary seed computed
from the left state. The guarantee retains the full left state, the original
right input to the initial-seed map, both refresh seeds, and the tampered
refresh output. Joint source envelopes pay only the displayed message
alphabet factors; no conditional source or intermediate seed guarantee is
assumed. Exact transcript factors remain normalized at null observations.

This is the terminal first-output step for the opposite-advice flip-flop
argument of Chattopadhyay--Goyal--Li, *Non-Malleable Extractors and Codes,
with their Many Tampered Extensions*, Algorithm 1 and the look-ahead
analysis in Lemma 6.5 and Claim 6.6, printed pp.25--29:
<https://arxiv.org/abs/1505.00107>. It uses the finite two-sided leakage
estimate underlying Chattopadhyay--Liao (2021), Lemma 3.26:
<https://arxiv.org/abs/2110.12652>. `FlipFlop.Opposite.False` and
`FlipFlop.Opposite.True` compose the complete flip-flop guarantee.
-/

public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B X Q Seed Mid Y Out : Type*}

/-- Every observed variable comes from the original joint law, with both original states preserved. -/
theorem fixedTampering_factored_eq_map
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    factoredWeight (fixedTamperingTranscriptWeight w l r x q y' leak initialSeed W R)
      (fixedTamperingLeft l x leak initialSeed W) (fixedTamperingRight r q y' R) =
      mapWeight (fun p : (Z × B) × A =>
        ((fixedTamperingTranscriptValue x q y' leak initialSeed W R p.1.1 p.2 p.1.2,
          p.1.2), p.2)) (factoredWeight w l r) :=
  Internal.fixedTampering_factored_eq_map w l r x q y' leak initialSeed W R hl hr

/-- The final transcript and both conditional kernels are normalized, including impossible rows. -/
theorem fixedTampering_factors_probability
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (fixedTamperingTranscriptWeight w l r x q y' leak initialSeed W R) ∧
      (∀ t : FixedTamperingTranscript Z Q Mid Out,
        IsProbabilityWeight (fixedTamperingLeft l x leak initialSeed W t)) ∧
      (∀ t, IsProbabilityWeight (fixedTamperingRight r q y' R t)) :=
  Internal.fixedTampering_factors_probability w l r x q y' leak initialSeed W R hw hl hr

/-- The actual refresh is a probability law for normalized original factors. -/
theorem fixedTamperingRefreshWeight_probability
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R) :=
  Internal.fixedTamperingRefreshWeight_probability w l r x q y y' leak initialSeed W R hw hl hr

/-- The refresh uses the original right source and the honest seed recorded in the exact transcript. -/
theorem fixedTamperingRefreshWeight_eq_factored
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R =
      mapWeight (fun p : (FixedTamperingTranscript Z Q Mid Out × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1.1 p.1.2) p.1.1.2))
        (factoredWeight (fixedTamperingTranscriptWeight w l r x q y' leak initialSeed W R)
          (fixedTamperingLeft l x leak initialSeed W) (fixedTamperingRight r q y' R)) :=
  Internal.fixedTamperingRefreshWeight_eq_factored w l r x q y y' leak initialSeed W R hl hr

/-- Two actual extraction calls tolerate an arbitrary left-only tampered seed. -/
theorem WeightedStrongSeededExtractor.fixedTampering_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {R : Y → Mid → Out} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (refresh : WeightedStrongSeededExtractor R L η) (refresh_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)
      (uniformSecondWeight
        (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)) ≤
          η + ε + δ + (K : ℝ) * Fintype.card Mid * (∑ z, μ z) +
            (L : ℝ) * Fintype.card Q * Fintype.card Out * ∑ z, ν z :=
  Internal.weightedStrongSeededExtractor_fixedTampering_dist_le
    first first_error refresh refresh_error w l r x q y y' leak initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed

/-- A combined joint-envelope budget bounds both observation losses. -/
theorem WeightedStrongSeededExtractor.fixedTampering_dist_le_of_budget
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {R : Y → Mid → Out} {K L : Nat} {ε η δ ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (refresh : WeightedStrongSeededExtractor R L η) (refresh_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ)
    (budget : (K : ℝ) * Fintype.card Mid * (∑ z, μ z) +
      (L : ℝ) * Fintype.card Q * Fintype.card Out * (∑ z, ν z) ≤ ρ) :
    weightDist (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)
      (uniformSecondWeight
        (fixedTamperingRefreshWeight w l r x q y y' leak initialSeed W R)) ≤
          η + ε + δ + ρ :=
  Internal.weightedStrongSeededExtractor_fixedTampering_dist_le_of_budget
    first first_error refresh refresh_error w l r x q y y' leak initialSeed μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed budget

end Algebraic.Cutwidth.Extractor
