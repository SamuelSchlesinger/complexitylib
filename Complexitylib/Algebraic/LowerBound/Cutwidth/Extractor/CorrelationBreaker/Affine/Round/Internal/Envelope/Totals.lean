/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Mathlib.Tactic.Ring

/-!
# Exact envelope totals and signs in one affine round

There are two left messages and four short right messages, counting the
paired middle-right observation twice. Thus the full original-left and
original-right envelope totals are multiplied by the square and fourth
power of the short-message alphabet size, respectively. Opposite-side
observations preserve totals exactly rather than introducing extra factors.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundPrefixMaskLeftEnvelope_sum (h t L : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affineRoundPrefixMaskLeftEnvelope h t L μ r wr z) = ∑ z, μ z :=
  observedTranscript_right_envelope_sum μ r _ hr

theorem affineRoundPrefixLeftEnvelope_sum (h t L : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affineRoundPrefixLeftEnvelope h t L μ r wr z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) * ∑ z, μ z := by
  unfold affineRoundPrefixLeftEnvelope
  rw [observedTranscript_left_envelope_sum, affineRoundPrefixMaskLeftEnvelope_sum h t L μ r wr hr]

theorem affineRoundPrefixRightEnvelope_sum (h t L : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affineRoundPrefixRightEnvelope h t L ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) * ∑ z, ξ z := by
  unfold affineRoundPrefixRightEnvelope
  rw [observedTranscript_right_envelope_sum
    (fun z : AffineRoundPrefixMaskTranscript Z t L => ξ z.1) (fun z => l z.1)
    (affineRoundPrefixLeftMessage h t L wl) (fun z => hl z.1),
    observedTranscript_left_envelope_sum]

theorem affineRoundMiddleRightLeftEnvelope_sum (d h t L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) * ∑ z, μ z := by
  have hr₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) :=
    fun z => observedTranscriptKernel_probability _ _ hr z.1
  have total := observedTranscript_right_envelope_sum (affineRoundPrefixLeftEnvelope h t L μ r wr)
    (affineRoundPrefixRight h t L r wr) (affineRoundMiddleRightMessage d h t L e wr ys)
    (fun z => (hr₁ z).2)
  exact total.trans (affineRoundPrefixLeftEnvelope_sum h t L μ r wr (fun z => (hr z).2))

theorem affineRoundMiddleRightRightEnvelope_sum (h t L : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affineRoundMiddleRightRightEnvelope h t L ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 3 * ∑ z, ξ z := by
  unfold affineRoundMiddleRightRightEnvelope
  rw [observedTranscript_left_envelope_sum, affineRoundPrefixRightEnvelope_sum h t L ξ l wl hl]
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

theorem affineRoundMiddleLeftEnvelope_sum (d h t L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affineRoundMiddleLeftEnvelope d h t L e μ r wr ys z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z := by
  unfold affineRoundMiddleLeftEnvelope
  rw [observedTranscript_left_envelope_sum,
    affineRoundMiddleRightLeftEnvelope_sum d h t L e μ r wr ys hr]
  ring

theorem affineRoundMiddleRightEnvelope_sum (h t L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ z, affineRoundMiddleRightEnvelope h t L e ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 3 * ∑ z, ξ z := by
  have hl₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixLeft h t L l wl z) :=
    observedTranscriptKernel_probability _ _ (fun z => hl z.1)
  have total := observedTranscript_right_envelope_sum (affineRoundMiddleRightRightEnvelope h t L ξ l wl)
    (fun z : AffineRoundMiddleRightTranscript Z t L => affineRoundPrefixLeft h t L l wl z.1)
    (affineRoundMiddleLeftMessage h t L e wl) (fun z => (hl₁ z.1).2)
  exact total.trans (affineRoundMiddleRightRightEnvelope_sum h t L ξ l wl (fun z => (hl z).2))

theorem affineRoundTranscriptLeftEnvelope_sum (d h t L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affineRoundTranscriptLeftEnvelope d h t L e μ r wr ys z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z := by
  have hr₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) :=
    fun z => observedTranscriptKernel_probability _ _ hr z.1
  have hr₂ : ∀ z, IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z) :=
    observedTranscriptKernel_probability _ _ hr₁
  have total := observedTranscript_right_envelope_sum
    (affineRoundMiddleLeftEnvelope d h t L e μ r wr ys)
    (fun z : AffineRoundMiddleTranscript Z t L =>
      affineRoundMiddleRightKernel d h t L e r wr ys z.1)
    (affineRoundFinalSeedRight d t L e ys) (fun z => (hr₂ z.1).2)
  exact total.trans (affineRoundMiddleLeftEnvelope_sum d h t L e μ r wr ys hr)

theorem affineRoundTranscriptRightEnvelope_sum (h t L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ z, affineRoundTranscriptRightEnvelope h t L e ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 4 * ∑ z, ξ z := by
  unfold affineRoundTranscriptRightEnvelope
  rw [observedTranscript_left_envelope_sum, affineRoundMiddleRightEnvelope_sum h t L e ξ l wl hl]
  ring

theorem affineRoundPrefixLeftEnvelope_nonnegative (h t L : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z b, 0 ≤ r z b)
    (z : AffineRoundPrefixTranscript Z t L) :
    0 ≤ affineRoundPrefixLeftEnvelope h t L μ r wr z :=
  observedTranscriptWeight_nonnegative _ _ _ nonnegative hr z.1

theorem affineRoundPrefixRightEnvelope_nonnegative (h t L : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffineRoundPrefixTranscript Z t L) :
    0 ≤ affineRoundPrefixRightEnvelope h t L ξ l wl z :=
  observedTranscriptWeight_nonnegative
    (fun z : AffineRoundPrefixMaskTranscript Z t L => ξ z.1) (fun z => l z.1)
    (affineRoundPrefixLeftMessage h t L wl) (fun z => nonnegative z.1) (fun z => hl z.1) z

theorem affineRoundMiddleRightLeftEnvelope_nonnegative (d h t L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (z : AffineRoundMiddleRightTranscript Z t L) :
    0 ≤ affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys z := by
  have hr₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) :=
    fun z => observedTranscriptKernel_probability _ _ hr z.1
  exact observedTranscriptWeight_nonnegative _ _ _
    (affineRoundPrefixLeftEnvelope_nonnegative h t L μ r wr nonnegative (fun z => (hr z).1))
    (fun z => (hr₁ z).1) z

theorem affineRoundMiddleRightRightEnvelope_nonnegative (h t L : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffineRoundMiddleRightTranscript Z t L) :
    0 ≤ affineRoundMiddleRightRightEnvelope h t L ξ l wl z :=
  affineRoundPrefixRightEnvelope_nonnegative h t L ξ l wl nonnegative hl z.1

theorem affineRoundMiddleLeftEnvelope_nonnegative (d h t L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (z : AffineRoundMiddleTranscript Z t L) :
    0 ≤ affineRoundMiddleLeftEnvelope d h t L e μ r wr ys z :=
  affineRoundMiddleRightLeftEnvelope_nonnegative d h t L e μ r wr ys nonnegative hr z.1

theorem affineRoundMiddleRightEnvelope_nonnegative (h t L e : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z, IsProbabilityWeight (l z))
    (z : AffineRoundMiddleTranscript Z t L) :
    0 ≤ affineRoundMiddleRightEnvelope h t L e ξ l wl z := by
  have hl₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixLeft h t L l wl z) :=
    observedTranscriptKernel_probability _ _ (fun z => hl z.1)
  exact observedTranscriptWeight_nonnegative _ _ _
    (affineRoundMiddleRightRightEnvelope_nonnegative h t L ξ l wl nonnegative
      (fun z => (hl z).1)) (fun z => (hl₁ z.1).1) z

theorem affineRoundTranscriptLeftEnvelope_nonnegative (d h t L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (z : AffineRoundTranscript Z t L) :
    0 ≤ affineRoundTranscriptLeftEnvelope d h t L e μ r wr ys z := by
  have hr₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) :=
    fun z => observedTranscriptKernel_probability _ _ hr z.1
  have hr₂ : ∀ z, IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z) :=
    observedTranscriptKernel_probability _ _ hr₁
  exact observedTranscriptWeight_nonnegative _ _ _
    (affineRoundMiddleLeftEnvelope_nonnegative d h t L e μ r wr ys nonnegative hr)
    (fun z => (hr₂ z.1).1) z

theorem affineRoundTranscriptRightEnvelope_nonnegative (h t L e : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z, IsProbabilityWeight (l z))
    (z : AffineRoundTranscript Z t L) :
    0 ≤ affineRoundTranscriptRightEnvelope h t L e ξ l wl z :=
  affineRoundMiddleRightEnvelope_nonnegative h t L e ξ l wl nonnegative hl z.1

theorem card_affineRoundShortMessages (t L : Nat) :
    Fintype.card (AffineRoundShortMessages t L) = 2 ^ (matchedBlockSeedBits L * (t + 1)) := by
  simp only [AffineRoundShortMessages, AffinePhaseOneCopies, Fintype.card_fun,
    Fintype.card_option, Fintype.card_fin, Fintype.card_bool, pow_mul]

end Algebraic.Cutwidth.Extractor.Internal
