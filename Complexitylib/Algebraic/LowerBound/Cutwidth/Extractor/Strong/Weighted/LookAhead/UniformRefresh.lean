/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Internal.Basic

/-!
# Refresh from either output of an actual look-ahead

A nearly uniform honest right state suffices for the selected refresh.
The theorem keeps the complete common look-ahead history and original left
state. The tampered right state may be arbitrarily correlated with the
honest state; no conditioned cap for either current state is assumed.
Original left and right source envelopes are averaged over the transcript.

The proof repairs the honest state inside the correlated original right
state and preserves the original source marginals. Comparing the final law
with its actual retained marginal charges twice the original discrepancy.
Exact factorization identifies the refreshed value as right-only after the
common history is observed, including on completed null rows.

This supplies a single refresh step for the advice-chain analysis of
Chattopadhyay--Goyal--Li, *Non-Malleable Extractors and Codes, with their Many
Tampered Extensions*, Algorithm 2 and Claim 6.11, printed pp.31--32:
<https://arxiv.org/pdf/1505.00107>. The finite repair and explicit average
error estimate are the deductions formalized here; iterating the advice
chain remains a separate theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The selected refresh and its complete retained history have a normalized actual law. -/
theorem lookAheadSelectedRefreshWeight_probability {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) (second : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R second) :=
  Internal.lookAheadSelectedRefreshWeight_probability
    w l r x x' q q' initialSeed W QExt y R second hw hl hr

/-- Either refresh uses a seed fixed by the same exact common transcript. -/
theorem lookAheadSelectedRefreshWeight_eq_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) (second : Bool)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R second =
      mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1 p.1.2)
          (if second then p.1.1.2.1.2 else p.1.1.2.1.1)))
        (factoredWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
          (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q')) :=
  Internal.lookAheadSelectedRefreshWeight_eq_factored
    w l r x x' q q' initialSeed W QExt y R second hl hr

/-- Dropping the left state gives the exact refreshed seed law over the common transcript. -/
theorem lookAheadSelectedRefreshWeight_retainedSeed {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out) (second : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × A) × Out => (p.1.1, p.2))
        (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R second) =
      retainedSeedWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
        (lookAheadBaseRight r q q')
        (fun t b => R (y t.1.1 b) (if second then t.2.1.2 else t.2.1.1)) :=
  Internal.lookAheadSelectedRefreshWeight_retainedSeed
    w l r x x' q q' initialSeed W QExt y R second hl hr

/-- Either selected refresh needs only average uniformity of its actual honest state. -/
theorem WeightedStrongSeededExtractor.lookAhead_uniformRefresh_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {R : Y → Mid → Out}
    {K L J : Nat} {ε η θ ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (refresh : WeightedStrongSeededExtractor R J θ) (refresh_error : 0 ≤ θ)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (y : Z → B → Y) (μ ξ : Z → ℝ) (chooseSecond : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    weightDist
        (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R chooseSecond)
        (uniformSecondWeight
          (lookAheadSelectedRefreshWeight w l r x x' q q' initialSeed W QExt y R chooseSecond)) ≤
      θ + 2 * ε + η + 2 * ρ +
        (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) / Fintype.card Q +
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z :=
  Internal.weightedStrongSeededExtractor_lookAhead_uniformRefresh_dist_le
    first first_error second second_error refresh refresh_error w l r x x' q q' initialSeed
    y μ ξ chooseSecond hw hl hr left_nonnegative right_nonnegative left_cap right_cap balanced state

end Algebraic.Cutwidth.Extractor
