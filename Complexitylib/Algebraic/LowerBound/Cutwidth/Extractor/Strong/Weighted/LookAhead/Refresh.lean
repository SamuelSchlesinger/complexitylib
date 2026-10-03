/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.Envelope
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.Factorization
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.First
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Internal.Second

/-!
# Actual first refreshes in the opposite-advice flip-flop argument

The common transcript records the right input pair and all four first
look-ahead outputs. Each refresh reads the original right source. The
first-output refresh retains this transcript and the full left state.
The second-output refresh additionally retains the tampered refresh
seeded by the tampered first output.

The seed errors are derived from the original first extraction or the
actual two-round look-ahead theorem. The only seed-discrepancy hypothesis
concerns the original prefix. Source hypotheses are joint envelopes,
not bounds on every conditional row. The four left outputs are appended
after extraction using the retained left state, so no seed is assumed
uniform after revealing itself. Exact observation laws and envelope totals
support subsequent repair and extraction steps.

These are finite first-phase steps in Chattopadhyay--Goyal--Li,
*Non-Malleable Extractors and Codes, with their Many Tampered Extensions*
(2015), Algorithm 1 and the proof of Lemma 6.8, printed pp.28--30:
<https://arxiv.org/pdf/1505.00107>. The complete opposite-advice security
argument and its iteration are separate results.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Recording the right pair and all four left outputs preserves the full factored joint law. -/
theorem lookAheadBase_factored {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      let zq := (p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2))
      (((zq, lookAheadBaseMessage x x' initialSeed W QExt zq p.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
        (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q') :=
  Internal.lookAheadBase_factored
    w l r x x' q q' initialSeed W QExt hl hr

/-- The common transcript and both conditional kernels are normalized, including null rows. -/
theorem lookAheadBase_probability {Z A B X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt) ∧
      (∀ t, IsProbabilityWeight (lookAheadBaseLeft l x x' initialSeed W QExt t)) ∧
      (∀ t, IsProbabilityWeight (lookAheadBaseRight (Mid := Mid) r q q' t)) :=
  Internal.lookAheadBase_probability
    w l r x x' q q' initialSeed W QExt hw hl hr

/-- The first-output refresh and its complete retained state have a normalized actual law. -/
theorem lookAheadFirstRefreshWeight_probability {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R) :=
  Internal.lookAheadFirstRefreshWeight_probability
    w l r x x' q q' initialSeed W QExt y R hw hl hr

/-- The second-output refresh, stored tampered refresh, and left state are normalized. -/
theorem lookAheadTamperedRefreshWeight_probability {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y y' : Z → B → Y) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R) :=
  Internal.lookAheadTamperedRefreshWeight_probability
    w l r x x' q q' initialSeed W QExt y y' R hw hl hr

/-- The common transcript preserves nonnegativity of the left source envelope. -/
theorem lookAheadBaseLeftEnvelope_nonnegative {Z B Q Mid : Type*} [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ) (q q' : Z → B → Q)
    (hμ : ∀ z, 0 ≤ μ z) (hr : ∀ z b, 0 ≤ r z b)
    (t : LookAheadBaseTranscript Z Q Mid) :
    0 ≤ lookAheadBaseLeftEnvelope μ r q q' t :=
  Internal.lookAheadBaseLeftEnvelope_nonnegative
    μ r q q' hμ hr t

/-- The common transcript preserves nonnegativity of the right source envelope. -/
theorem lookAheadBaseRightEnvelope_nonnegative {Z A X Q Seed Mid : Type*} [Fintype A]
    (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hν : ∀ z, 0 ≤ ν z) (hl : ∀ z a, 0 ≤ l z a)
    (t : LookAheadBaseTranscript Z Q Mid) :
    0 ≤ lookAheadBaseRightEnvelope ν l x x' initialSeed W QExt t :=
  Internal.lookAheadBaseRightEnvelope_nonnegative
    ν l x x' initialSeed W QExt hν hl t

/-- The original left source has the stated joint envelope under the common transcript. -/
theorem lookAheadBase_left_envelope {Z A B X Q Seed Mid : Type*}
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (μ : Z → ℝ)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (t : LookAheadBaseTranscript Z Q Mid) (x₀ : X) :
    lookAheadBaseWeight w l r x x' q q' initialSeed W QExt t *
        mapWeight (x t.1.1) (lookAheadBaseLeft l x x' initialSeed W QExt t) x₀ ≤
      lookAheadBaseLeftEnvelope μ r q q' t :=
  Internal.lookAheadBase_left_envelope
    w l r x x' q q' initialSeed W QExt μ hw hl hr cap t x₀

/-- The original right source has the stated joint envelope under the common transcript. -/
theorem lookAheadBase_right_envelope {Z A B X Q Seed Mid Y : Type*}
    [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (y : Z → B → Y) (ν : Z → ℝ)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (t : LookAheadBaseTranscript Z Q Mid) (y₀ : Y) :
    lookAheadBaseWeight w l r x x' q q' initialSeed W QExt t *
        mapWeight (y t.1.1) (lookAheadBaseRight r q q' t) y₀ ≤
      lookAheadBaseRightEnvelope ν l x x' initialSeed W QExt t :=
  Internal.lookAheadBase_right_envelope
    w l r x x' q q' initialSeed W QExt y ν hw hl hr cap t y₀

/-- The total left source envelope pays only for the four-output left message alphabet. -/
theorem lookAheadBaseLeftEnvelope_sum {Z B Q Mid : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Mid]
    (μ : Z → ℝ) (r : Z → B → ℝ) (q q' : Z → B → Q)
    (mass : ∀ z, ∑ b, r z b = 1) :
    (∑ t : LookAheadBaseTranscript Z Q Mid, lookAheadBaseLeftEnvelope μ r q q' t) =
      (Fintype.card ((Mid × Mid) × (Mid × Mid)) : ℝ) * ∑ z, μ z :=
  Internal.lookAheadBaseLeftEnvelope_sum
    μ r q q' mass

/-- The total right source envelope pays only for the right-input pair alphabet. -/
theorem lookAheadBaseRightEnvelope_sum {Z A X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype Q] [Fintype Mid]
    (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (mass : ∀ z, ∑ a, l z a = 1) :
    (∑ t, lookAheadBaseRightEnvelope ν l x x' initialSeed W QExt t) =
      (Fintype.card (Q × Q) : ℝ) * ∑ z, ν z :=
  Internal.lookAheadBaseRightEnvelope_sum
    ν l x x' initialSeed W QExt mass

/-- The first refresh is a right-only map once the common transcript fixes its seed. -/
theorem lookAheadFirstRefreshWeight_eq_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R =
      mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1 p.1.2) p.1.1.2.1.1))
        (factoredWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
          (lookAheadBaseLeft l x x' initialSeed W QExt) (lookAheadBaseRight r q q')) :=
  Internal.lookAheadFirstRefreshWeight_eq_factored
    w l r x x' q q' initialSeed W QExt y R hl hr

/-- Dropping the left state gives the exact refreshed seed law over the common transcript. -/
theorem lookAheadFirstRefreshWeight_retainedSeed {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (LookAheadBaseTranscript Z Q Mid × A) × Out => (p.1.1, p.2))
        (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R) =
      retainedSeedWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
        (lookAheadBaseRight r q q') (fun t b => R (y t.1.1 b) t.2.1.1) :=
  Internal.lookAheadFirstRefreshWeight_retainedSeed
    w l r x x' q q' initialSeed W QExt y R hl hr

/-- Revealing the tampered refresh preserves an exact successive-observation factorization. -/
theorem lookAheadTamperedRefresh_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y' : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      let zq := (p.1.1, (q p.1.1 p.1.2, q' p.1.1 p.1.2))
      let messages := lookAheadBaseMessage x x' initialSeed W QExt zq p.2
      ((((zq, messages), R (y' p.1.1 p.1.2) messages.2.1), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (observedTranscriptWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
          (lookAheadBaseRight r q q') (fun t b => R (y' t.1.1 b) t.2.2.1))
        (fun tu => lookAheadBaseLeft l x x' initialSeed W QExt tu.1)
        (observedTranscriptKernel (lookAheadBaseRight r q q')
          (fun t b => R (y' t.1.1 b) t.2.2.1)) :=
  Internal.lookAheadTamperedRefresh_factored
    w l r x x' q q' initialSeed W QExt y' R hl hr

/-- The second refresh is right-only after the common transcript and tampered refresh. -/
theorem lookAheadTamperedRefreshWeight_eq_factored {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (y y' : Z → B → Y) (R : Y → Mid → Out)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R =
      mapWeight (fun p : ((LookAheadBaseTranscript Z Q Mid × Out) × B) × A =>
        ((p.1.1, p.2), R (y p.1.1.1.1.1 p.1.2) p.1.1.1.2.1.2))
        (factoredWeight
          (observedTranscriptWeight (lookAheadBaseWeight w l r x x' q q' initialSeed W QExt)
            (lookAheadBaseRight r q q') (fun t b => R (y' t.1.1 b) t.2.2.1))
          (fun tu => lookAheadBaseLeft l x x' initialSeed W QExt tu.1)
          (observedTranscriptKernel (lookAheadBaseRight r q q')
            (fun t b => R (y' t.1.1 b) t.2.2.1))) :=
  Internal.lookAheadTamperedRefreshWeight_eq_factored
    w l r x x' q q' initialSeed W QExt y y' R hl hr

/-- The actual first-output refresh is nearly uniform given the full left state and transcript. -/
theorem WeightedStrongSeededExtractor.lookAhead_first_refresh_dist_le
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {R : Y → Mid → Out} {K J : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (refresh : WeightedStrongSeededExtractor R J η) (refresh_error : 0 ≤ η)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (QExt : Q → Mid → Seed) (y : Z → B → Y) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R)
      (uniformSecondWeight
        (lookAheadFirstRefreshWeight w l r x x' q q' initialSeed W QExt y R)) ≤
      η + (ε + δ + (K : ℝ) * ∑ z, μ z) +
        (J : ℝ) * Fintype.card (Q × Q) * ∑ z, ν z :=
  Internal.weightedStrongSeededExtractor_lookAhead_first_refresh_dist_le
    first first_error refresh refresh_error w l r x x' q q' initialSeed QExt y μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed

/-- The actual second-output refresh is nearly uniform even retaining the tampered first refresh. -/
theorem WeightedStrongSeededExtractor.lookAhead_tampered_refresh_dist_le
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
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (y y' : Z → B → Y) (μ ν ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (refresh_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (refresh_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => initialSeed (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r (fun z b => initialSeed (q z b)))) ≤ δ) :
    weightDist (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R)
      (uniformSecondWeight
        (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R)) ≤
      θ + (2 * ε + η + δ + (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) * ∑ z, ν z) +
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z :=
  Internal.weightedStrongSeededExtractor_lookAhead_tampered_refresh_dist_le
    first first_error second second_error refresh refresh_error
    w l r x x' q q' initialSeed y y' μ ν ξ hw hl hr
    left_nonnegative right_nonnegative refresh_nonnegative left_cap right_cap refresh_cap seed

end Algebraic.Cutwidth.Extractor
