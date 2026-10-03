/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Internal.Envelope.Bounds
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Internal.Envelope.Totals

/-!
# Exact source-envelope accounting for one affine round

Original left and right source coordinates retain joint mass envelopes
through every actual observation. If `S` is the cardinality of all honest
and tampered short messages, the complete left total is multiplied by
`S^2`, and the complete right total by `S^4`. Opposite-side observations
preserve envelope totals exactly. Null conditional rows are included.

These finite bounds implement the transcript entropy accounting in
Chattopadhyay--Liao, Theorem 6.1, printed pp.23--25:
<https://arxiv.org/abs/2110.12652>. They neither supply nor assume a
statistical security guarantee for the round's extractor calls.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The first right observation scales the original-left envelope by its message probability. -/
theorem affineRoundPrefixMask_left_envelope (h t L : Nat) {Z A B X : Type*}
    [Fintype A] [Fintype B] (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (x : Z → A → X) (μ : Z → ℝ) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffineRoundPrefixMaskTranscript Z t L) (x₀ : X) :
    affineRoundPrefixMaskWeight h t L w r wr z * mapWeight (x z.1) (l z.1) x₀ ≤
      affineRoundPrefixMaskLeftEnvelope h t L μ r wr z :=
  Internal.affineRoundPrefixMask_left_envelope h t L w l r wr x μ hr cap z x₀

/-- The original-right source is bounded by the copied envelope after its prefix masks are observed. -/
theorem affineRoundPrefixMask_right_envelope (h t L : Nat) {Z B Y : Type*}
    [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (y : Z → B → Y) (ξ : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffineRoundPrefixMaskTranscript Z t L) (y₀ : Y) :
    affineRoundPrefixMaskWeight h t L w r wr z *
        mapWeight (y z.1) (affineRoundPrefixMaskRight h t L r wr z) y₀ ≤ ξ z.1 :=
  Internal.affineRoundPrefixMask_right_envelope h t L w r wr y ξ hw hr cap z y₀

/-- Actual prefixes copy the original-left envelope over their message alphabet. -/
theorem affineRoundPrefix_left_envelope (h t L : Nat) {Z A B X : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (x : Z → A → X) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffineRoundPrefixTranscript Z t L) (x₀ : X) :
    affineRoundPrefixWeight h t L w l r wl wr z *
        mapWeight (x z.1.1) (affineRoundPrefixLeft h t L l wl z) x₀ ≤
      affineRoundPrefixLeftEnvelope h t L μ r wr z :=
  Internal.affineRoundPrefix_left_envelope h t L w l r wl wr x μ hw hl hr cap z x₀

/-- The opposite-side prefix observation preserves the weighted original-right bound. -/
theorem affineRoundPrefix_right_envelope (h t L : Nat) {Z A B Y : Type*}
    [Fintype A] [Fintype B] (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (y : Z → B → Y) (ξ : Z → ℝ)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffineRoundPrefixTranscript Z t L) (y₀ : Y) :
    affineRoundPrefixWeight h t L w l r wl wr z *
        mapWeight (y z.1.1) (affineRoundPrefixRight h t L r wr z) y₀ ≤
      affineRoundPrefixRightEnvelope h t L ξ l wl z :=
  Internal.affineRoundPrefix_right_envelope h t L w l r wl wr y ξ hw hl hr cap z y₀

/-- First right seeds and short-row masks preserve the original-left source bound. -/
theorem affineRoundMiddleRight_left_envelope (d h t L e : Nat) {Z A B X : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (x : Z → A → X) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffineRoundMiddleRightTranscript Z t L) (x₀ : X) :
    affineRoundMiddleRightWeight d h t L e w l r wl wr ys z *
        mapWeight (x z.1.1.1) (affineRoundPrefixLeft h t L l wl z.1) x₀ ≤
      affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys z :=
  Internal.affineRoundMiddleRight_left_envelope d h t L e w l r wl wr ys x μ hw hl hr cap z x₀

/-- The paired middle-right observation copies the original-right source envelope. -/
theorem affineRoundMiddleRight_right_envelope (d h t L e : Nat) {Z A B Y : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (y : Z → B → Y) (ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffineRoundMiddleRightTranscript Z t L) (y₀ : Y) :
    affineRoundMiddleRightWeight d h t L e w l r wl wr ys z *
        mapWeight (y z.1.1.1) (affineRoundMiddleRightKernel d h t L e r wr ys z) y₀ ≤
      affineRoundMiddleRightRightEnvelope h t L ξ l wl z :=
  Internal.affineRoundMiddleRight_right_envelope d h t L e w l r wl wr ys y ξ hw hl hr cap z y₀

/-- Actual short rows copy the original-left source envelope a second time. -/
theorem affineRoundMiddle_left_envelope (d h t L e : Nat) {Z A B X : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (x : Z → A → X) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffineRoundMiddleTranscript Z t L) (x₀ : X) :
    affineRoundMiddleWeight d h t L e w l r wl wr ys z *
        mapWeight (x z.1.1.1.1) (affineRoundMiddleLeft h t L e l wl z) x₀ ≤
      affineRoundMiddleLeftEnvelope d h t L e μ r wr ys z :=
  Internal.affineRoundMiddle_left_envelope d h t L e w l r wl wr ys x μ hw hl hr cap z x₀

/-- The short-row observation preserves the weighted original-right bound. -/
theorem affineRoundMiddle_right_envelope (d h t L e : Nat) {Z A B Y : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (y : Z → B → Y) (ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffineRoundMiddleTranscript Z t L) (y₀ : Y) :
    affineRoundMiddleWeight d h t L e w l r wl wr ys z *
        mapWeight (y z.1.1.1.1) (affineRoundMiddleRightKernel d h t L e r wr ys z.1) y₀ ≤
      affineRoundMiddleRightEnvelope h t L e ξ l wl z :=
  Internal.affineRoundMiddle_right_envelope d h t L e w l r wl wr ys y ξ hw hl hr cap z y₀

/-- The full actual transcript bounds the unchanged original-left source coordinates. -/
theorem affineRoundTranscript_left_envelope (d h t L e : Nat) {Z A B X : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (x : Z → A → X) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffineRoundTranscript Z t L) (x₀ : X) :
    affineRoundTranscriptWeight d h t L e w l r wl wr ys z *
        mapWeight (x z.1.1.1.1.1) (affineRoundTranscriptLeft h t L e l wl z) x₀ ≤
      affineRoundTranscriptLeftEnvelope d h t L e μ r wr ys z :=
  Internal.affineRoundTranscript_left_envelope d h t L e w l r wl wr ys x μ hw hl hr cap z x₀

/-- The full actual transcript bounds the unchanged original-right source coordinates. -/
theorem affineRoundTranscript_right_envelope (d h t L e : Nat) {Z A B Y : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (y : Z → B → Y) (ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffineRoundTranscript Z t L) (y₀ : Y) :
    affineRoundTranscriptWeight d h t L e w l r wl wr ys z *
        mapWeight (y z.1.1.1.1.1) (affineRoundTranscriptRight d h t L e r wr ys z) y₀ ≤
      affineRoundTranscriptRightEnvelope h t L e ξ l wl z :=
  Internal.affineRoundTranscript_right_envelope d h t L e w l r wl wr ys y ξ hw hl hr cap z y₀

/-- The first right observation preserves the original-left envelope total exactly. -/
theorem affineRoundPrefixMaskLeftEnvelope_sum (h t L : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affineRoundPrefixMaskLeftEnvelope h t L μ r wr z) = ∑ z, μ z :=
  Internal.affineRoundPrefixMaskLeftEnvelope_sum h t L μ r wr hr

/-- The actual prefix family charges one short-message alphabet to the left total. -/
theorem affineRoundPrefixLeftEnvelope_sum (h t L : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hr : ∀ z, ∑ b, r z b = 1) :
    (∑ z, affineRoundPrefixLeftEnvelope h t L μ r wr z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) * ∑ z, μ z :=
  Internal.affineRoundPrefixLeftEnvelope_sum h t L μ r wr hr

/-- Through the prefix stage, the right total pays only for its prefix-mask family. -/
theorem affineRoundPrefixRightEnvelope_sum (h t L : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affineRoundPrefixRightEnvelope h t L ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) * ∑ z, ξ z :=
  Internal.affineRoundPrefixRightEnvelope_sum h t L ξ l wl hl

/-- The paired right message preserves the preceding original-left envelope total. -/
theorem affineRoundMiddleRightLeftEnvelope_sum (d h t L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) * ∑ z, μ z :=
  Internal.affineRoundMiddleRightLeftEnvelope_sum d h t L e μ r wr ys hr

/-- The paired right message gives a cubic short-message factor in the right total. -/
theorem affineRoundMiddleRightRightEnvelope_sum (h t L : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, ∑ a, l z a = 1) :
    (∑ z, affineRoundMiddleRightRightEnvelope h t L ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 3 * ∑ z, ξ z :=
  Internal.affineRoundMiddleRightRightEnvelope_sum h t L ξ l wl hl

/-- Through the actual short rows, the original-left total pays two short-message families. -/
theorem affineRoundMiddleLeftEnvelope_sum (d h t L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affineRoundMiddleLeftEnvelope d h t L e μ r wr ys z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z :=
  Internal.affineRoundMiddleLeftEnvelope_sum d h t L e μ r wr ys hr

/-- Actual short rows preserve the cubic original-right envelope total. -/
theorem affineRoundMiddleRightEnvelope_sum (h t L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ z, affineRoundMiddleRightEnvelope h t L e ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 3 * ∑ z, ξ z :=
  Internal.affineRoundMiddleRightEnvelope_sum h t L e ξ l wl hl

/-- The complete round multiplies the original-left envelope total by the square alphabet size. -/
theorem affineRoundTranscriptLeftEnvelope_sum (d h t L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ z, affineRoundTranscriptLeftEnvelope d h t L e μ r wr ys z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z :=
  Internal.affineRoundTranscriptLeftEnvelope_sum d h t L e μ r wr ys hr

/-- The complete round multiplies the original-right envelope total by the fourth power alphabet size. -/
theorem affineRoundTranscriptRightEnvelope_sum (h t L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ z, affineRoundTranscriptRightEnvelope h t L e ξ l wl z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 4 * ∑ z, ξ z :=
  Internal.affineRoundTranscriptRightEnvelope_sum h t L e ξ l wl hl

/-- Nonnegative original-left envelopes remain nonnegative after the prefix stage. -/
theorem affineRoundPrefixLeftEnvelope_nonnegative (h t L : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z b, 0 ≤ r z b)
    (z : AffineRoundPrefixTranscript Z t L) :
    0 ≤ affineRoundPrefixLeftEnvelope h t L μ r wr z :=
  Internal.affineRoundPrefixLeftEnvelope_nonnegative h t L μ r wr nonnegative hr z

/-- Nonnegative original-right envelopes remain nonnegative after the prefix stage. -/
theorem affineRoundPrefixRightEnvelope_nonnegative (h t L : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffineRoundPrefixTranscript Z t L) :
    0 ≤ affineRoundPrefixRightEnvelope h t L ξ l wl z :=
  Internal.affineRoundPrefixRightEnvelope_nonnegative h t L ξ l wl nonnegative hl z

/-- The middle-right update preserves the original-left envelope sign, including null rows. -/
theorem affineRoundMiddleRightLeftEnvelope_nonnegative (d h t L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (z : AffineRoundMiddleRightTranscript Z t L) :
    0 ≤ affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys z :=
  Internal.affineRoundMiddleRightLeftEnvelope_nonnegative d h t L e μ r wr ys nonnegative hr z

/-- The copied middle-right original-right envelope is nonnegative. -/
theorem affineRoundMiddleRightRightEnvelope_nonnegative (h t L : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z a, 0 ≤ l z a)
    (z : AffineRoundMiddleRightTranscript Z t L) :
    0 ≤ affineRoundMiddleRightRightEnvelope h t L ξ l wl z :=
  Internal.affineRoundMiddleRightRightEnvelope_nonnegative h t L ξ l wl nonnegative hl z

/-- The original-left envelope remains nonnegative after the actual short outputs. -/
theorem affineRoundMiddleLeftEnvelope_nonnegative (d h t L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (z : AffineRoundMiddleTranscript Z t L) :
    0 ≤ affineRoundMiddleLeftEnvelope d h t L e μ r wr ys z :=
  Internal.affineRoundMiddleLeftEnvelope_nonnegative d h t L e μ r wr ys nonnegative hr z

/-- The original-right envelope remains nonnegative after the actual short outputs. -/
theorem affineRoundMiddleRightEnvelope_nonnegative (h t L e : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z, IsProbabilityWeight (l z))
    (z : AffineRoundMiddleTranscript Z t L) :
    0 ≤ affineRoundMiddleRightEnvelope h t L e ξ l wl z :=
  Internal.affineRoundMiddleRightEnvelope_nonnegative h t L e ξ l wl nonnegative hl z

/-- The full original-left envelope is nonnegative at every transcript. -/
theorem affineRoundTranscriptLeftEnvelope_nonnegative (d h t L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (z : AffineRoundTranscript Z t L) :
    0 ≤ affineRoundTranscriptLeftEnvelope d h t L e μ r wr ys z :=
  Internal.affineRoundTranscriptLeftEnvelope_nonnegative d h t L e μ r wr ys nonnegative hr z

/-- The full original-right envelope is nonnegative at every transcript. -/
theorem affineRoundTranscriptRightEnvelope_nonnegative (h t L e : Nat) {Z A : Type*}
    [Fintype A] (ξ : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (nonnegative : ∀ z, 0 ≤ ξ z) (hl : ∀ z, IsProbabilityWeight (l z))
    (z : AffineRoundTranscript Z t L) :
    0 ≤ affineRoundTranscriptRightEnvelope h t L e ξ l wl z :=
  Internal.affineRoundTranscriptRightEnvelope_nonnegative h t L e ξ l wl nonnegative hl z

/-- The honest and tampered short-message family has the exact Boolean cardinality. -/
theorem card_affineRoundShortMessages (t L : Nat) :
    Fintype.card (AffineRoundShortMessages t L) = 2 ^ (matchedBlockSeedBits L * (t + 1)) :=
  Internal.card_affineRoundShortMessages t L

end Algebraic.Cutwidth.Extractor
