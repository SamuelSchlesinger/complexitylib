/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second.Internal.Basic

/-!
# A second-output refresh with an arbitrary left-only tampered seed

The honest refresh rereads the original right source, seeded by the actual
second look-ahead output. The tampered refresh uses an arbitrary seed computed
from the left state. The final guarantee retains that seed, the original right
input to the look-ahead, both honest look-ahead outputs, the tampered refresh,
and the full original left state. Only original joint source envelopes and the
original prefix-seed discrepancy are assumed.

Revealing a normalized left-only message preserves the average original seed
discrepancy exactly. It multiplies the original left envelope total by the
message alphabet size and leaves the right envelope totals unchanged. Null
observations require no conditional-positivity assumption.

This finite composition supports the already-distinct-advice analysis of
Chattopadhyay--Goyal--Li, *Non-Malleable Extractors and Codes, with their Many
Tampered Extensions*, Algorithm 1, Lemma 6.5 and Claim 6.6, printed pp.25--29:
<https://arxiv.org/abs/1505.00107>. It uses the finite two-sided leakage estimate
underlying Chattopadhyay--Liao (2021), Lemma 3.26:
<https://arxiv.org/abs/2110.12652>. The complete advice-chain invariant is
proved in `Advice.Extraction` (`adviceCorrelationBreaker_dist_le`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A normalized left-only observation preserves the average original right-seed discrepancy. -/
theorem retainedSeedWeight_observe_left_dist {Z A B U Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (f : Z → A → U) (s : Z → B → Seed)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (retainedSeedWeight (observedTranscriptWeight w l f)
      (fun zu => r zu.1) (fun zu => s zu.1))
      (uniformSecondWeight (retainedSeedWeight (observedTranscriptWeight w l f)
        (fun zu => r zu.1) (fun zu => s zu.1))) =
      weightDist (retainedSeedWeight w r s) (uniformSecondWeight (retainedSeedWeight w r s)) :=
  Internal.retainedSeedWeight_observe_left_dist w l r f s hw hl hr

/-- The second-output refresh is the probability law of the actual retained variables. -/
theorem fixedTamperingSecondRefreshWeight_probability
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (fixedTamperingSecondRefreshWeight w l r x q y y' leak initialSeed W QExt R) :=
  Internal.fixedTamperingSecondRefreshWeight_probability
    w l r x q y y' leak initialSeed W QExt R hw hl hr

/-- The actual two-round second output seeds a refresh against arbitrary left-only tampering. -/
theorem WeightedStrongSeededExtractor.fixedTampering_second_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {R : Y → Mid → Out}
    {K L J : Nat} {ε η θ δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (refresh : WeightedStrongSeededExtractor R J θ) (refresh_error : 0 ≤ θ)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed) (μ ν ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (refresh_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (refresh_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (fixedTamperingSecondRefreshWeight w l r x q y y' leak initialSeed W QExt R)
      (uniformSecondWeight
        (fixedTamperingSecondRefreshWeight w l r x q y y' leak initialSeed W QExt R)) ≤
      θ + 2 * ε + η + δ +
        (K : ℝ) * Fintype.card Mid * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) * (∑ z, ν z) +
        (J : ℝ) * Fintype.card Q * Fintype.card Out * ∑ z, ξ z :=
  Internal.weightedStrongSeededExtractor_fixedTampering_second_dist_le
    first first_error second second_error refresh refresh_error
    w l r x q y y' leak initialSeed μ ν ξ hw hl hr
    left_nonnegative right_nonnegative refresh_nonnegative left_cap right_cap refresh_cap seed

end Algebraic.Cutwidth.Extractor
