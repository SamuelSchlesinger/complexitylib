/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope

/-!
# Original-source envelopes under the common look-ahead transcript

The left source pays for the four left outputs, while its envelope is
scaled by the right-pair probability. The right source pays for the two
right inputs; the subsequent left observation preserves its total envelope.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem lookAheadBaseLeftEnvelope_nonnegative {Z B Q Mid : Type*} [Fintype B]
    (μ : Z → ℝ) (r : Z → B → ℝ) (q q' : Z → B → Q)
    (hμ : ∀ z, 0 ≤ μ z) (hr : ∀ z b, 0 ≤ r z b)
    (t : LookAheadBaseTranscript Z Q Mid) :
    0 ≤ lookAheadBaseLeftEnvelope μ r q q' t :=
  observedTranscriptWeight_nonnegative μ r _ hμ hr t.1

theorem lookAheadBaseRightEnvelope_nonnegative {Z A X Q Seed Mid : Type*} [Fintype A]
    (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (hν : ∀ z, 0 ≤ ν z) (hl : ∀ z a, 0 ≤ l z a)
    (t : LookAheadBaseTranscript Z Q Mid) :
    0 ≤ lookAheadBaseRightEnvelope ν l x x' initialSeed W QExt t :=
  observedTranscriptWeight_nonnegative (fun zq : Z × (Q × Q) => ν zq.1)
    (fun zq => l zq.1) (lookAheadBaseMessage x x' initialSeed W QExt)
    (fun zq => hν zq.1) (fun zq => hl zq.1) t

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
      lookAheadBaseLeftEnvelope μ r q q' t := by
  have first := observedTranscript_right_envelope w l r x
    (fun z b => (q z b, q' z b)) μ hr cap
  exact observedTranscript_left_envelope _ _ (fun zq => x zq.1)
    (lookAheadBaseMessage x x' initialSeed W QExt) _
    (observedTranscriptWeight_nonnegative w r _ hw hr) (fun zq => hl zq.1) first t x₀

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
      lookAheadBaseRightEnvelope ν l x x' initialSeed W QExt t := by
  have first := observedTranscript_left_envelope w r y
    (fun z b => (q z b, q' z b)) ν hw hr cap
  exact observedTranscript_right_envelope _ _ (fun zq => l zq.1) (fun zq => y zq.1)
    (lookAheadBaseMessage x x' initialSeed W QExt) (fun zq => ν zq.1)
    (fun zq => hl zq.1) first t y₀

theorem lookAheadBaseLeftEnvelope_sum {Z B Q Mid : Type*}
    [Fintype Z] [Fintype B] [Fintype Q] [Fintype Mid]
    (μ : Z → ℝ) (r : Z → B → ℝ) (q q' : Z → B → Q)
    (mass : ∀ z, ∑ b, r z b = 1) :
    (∑ t : LookAheadBaseTranscript Z Q Mid, lookAheadBaseLeftEnvelope μ r q q' t) =
      (Fintype.card ((Mid × Mid) × (Mid × Mid)) : ℝ) * ∑ z, μ z := by
  simp only [lookAheadBaseLeftEnvelope]
  rw [observedTranscript_left_envelope_sum,
    observedTranscript_right_envelope_sum μ r _ mass]

theorem lookAheadBaseRightEnvelope_sum {Z A X Q Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype Q] [Fintype Mid]
    (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → X) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed)
    (mass : ∀ z, ∑ a, l z a = 1) :
    (∑ t, lookAheadBaseRightEnvelope ν l x x' initialSeed W QExt t) =
      (Fintype.card (Q × Q) : ℝ) * ∑ z, ν z := by
  simp only [lookAheadBaseRightEnvelope]
  rw [observedTranscript_right_envelope_sum (fun zq : Z × (Q × Q) => ν zq.1)
    (fun zq => l zq.1) (lookAheadBaseMessage x x' initialSeed W QExt)
    (fun zq => mass zq.1),
    observedTranscript_left_envelope_sum]

end Algebraic.Cutwidth.Extractor.Internal
