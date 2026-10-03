/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Internal.Factorization
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope

/-!
# Original-source joint mass bounds at every round stage

Each bound follows the actual deterministic observation on its own side or
the opposite side. The source coordinate maps stay those of the original
latent states. Conditional kernels are used only through their checked
normalization and joint-mass identities, including null observations.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundPrefixMask_left_envelope (h t L : Nat) {Z A B X : Type*}
    [Fintype A] [Fintype B] (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (x : Z → A → X) (μ : Z → ℝ) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (z : AffineRoundPrefixMaskTranscript Z t L) (x₀ : X) :
    affineRoundPrefixMaskWeight h t L w r wr z * mapWeight (x z.1) (l z.1) x₀ ≤
      affineRoundPrefixMaskLeftEnvelope h t L μ r wr z :=
  observedTranscript_right_envelope w l r x _ μ hr cap z x₀

theorem affineRoundPrefixMask_right_envelope (h t L : Nat) {Z B Y : Type*}
    [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (y : Z → B → Y) (ξ : Z → ℝ) (hw : ∀ z, 0 ≤ w z) (hr : ∀ z b, 0 ≤ r z b)
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (z : AffineRoundPrefixMaskTranscript Z t L) (y₀ : Y) :
    affineRoundPrefixMaskWeight h t L w r wr z *
        mapWeight (y z.1) (affineRoundPrefixMaskRight h t L r wr z) y₀ ≤ ξ z.1 :=
  observedTranscript_left_envelope w r y _ ξ hw hr cap z y₀

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
      affineRoundPrefixLeftEnvelope h t L μ r wr z := by
  have hw₀ := (affineRoundPrefixMask_probability h t L w r wr hw hr).1
  exact observedTranscript_left_envelope (affineRoundPrefixMaskWeight h t L w r wr)
    (fun z => l z.1) (fun z => x z.1) (affineRoundPrefixLeftMessage h t L wl)
    (affineRoundPrefixMaskLeftEnvelope h t L μ r wr) hw₀.1 (fun z => (hl z.1).1)
    (affineRoundPrefixMask_left_envelope h t L w l r wr x μ
      (fun z => (hr z).1) cap) z x₀

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
  observedTranscript_right_envelope (affineRoundPrefixMaskWeight h t L w r wr)
    (affineRoundPrefixMaskRight h t L r wr) (fun z => l z.1) (fun z => y z.1)
    (affineRoundPrefixLeftMessage h t L wl) (fun z => ξ z.1) (fun z => hl z.1)
    (affineRoundPrefixMask_right_envelope h t L w r wr y ξ hw hr cap) z y₀

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
      affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys z := by
  have hr₁ := (affineRoundPrefix_probability h t L w l r wl wr hw hl hr).2.2
  exact observedTranscript_right_envelope (affineRoundPrefixWeight h t L w l r wl wr)
    (affineRoundPrefixLeft h t L l wl) (affineRoundPrefixRight h t L r wr)
    (fun z => x z.1.1) (affineRoundMiddleRightMessage d h t L e wr ys)
    (affineRoundPrefixLeftEnvelope h t L μ r wr) (fun z => (hr₁ z).1)
    (affineRoundPrefix_left_envelope h t L w l r wl wr x μ hw hl hr cap) z x₀

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
      affineRoundMiddleRightRightEnvelope h t L ξ l wl z := by
  obtain ⟨hw₁, _, hr₁⟩ := affineRoundPrefix_probability h t L w l r wl wr hw hl hr
  exact observedTranscript_left_envelope (affineRoundPrefixWeight h t L w l r wl wr)
    (affineRoundPrefixRight h t L r wr) (fun z => y z.1.1)
    (affineRoundMiddleRightMessage d h t L e wr ys)
    (affineRoundPrefixRightEnvelope h t L ξ l wl) hw₁.1 (fun z => (hr₁ z).1)
    (affineRoundPrefix_right_envelope h t L w l r wl wr y ξ hw.1
      (fun z => (hl z).1) (fun z => (hr z).1) cap) z y₀

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
      affineRoundMiddleLeftEnvelope d h t L e μ r wr ys z := by
  obtain ⟨hw₂, hl₂, _⟩ :=
    affineRoundMiddleRight_probability d h t L e w l r wl wr ys hw hl hr
  exact observedTranscript_left_envelope (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundPrefixLeft h t L l wl z.1) (fun z => x z.1.1.1)
    (affineRoundMiddleLeftMessage h t L e wl)
    (affineRoundMiddleRightLeftEnvelope d h t L e μ r wr ys) hw₂.1 (fun z => (hl₂ z).1)
    (affineRoundMiddleRight_left_envelope d h t L e w l r wl wr ys x μ hw hl hr cap) z x₀

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
      affineRoundMiddleRightEnvelope h t L e ξ l wl z := by
  have hl₂ := (affineRoundMiddleRight_probability d h t L e w l r wl wr ys hw hl hr).2.1
  exact observedTranscript_right_envelope (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
    (affineRoundMiddleRightKernel d h t L e r wr ys)
    (fun z => affineRoundPrefixLeft h t L l wl z.1) (fun z => y z.1.1.1)
    (affineRoundMiddleLeftMessage h t L e wl) (affineRoundMiddleRightRightEnvelope h t L ξ l wl)
    (fun z => (hl₂ z).1)
    (affineRoundMiddleRight_right_envelope d h t L e w l r wl wr ys y ξ hw hl hr cap) z y₀

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
      affineRoundTranscriptLeftEnvelope d h t L e μ r wr ys z := by
  have hr₃ := (affineRoundMiddle_probability d h t L e w l r wl wr ys hw hl hr).2.2
  exact observedTranscript_right_envelope (affineRoundMiddleWeight d h t L e w l r wl wr ys)
    (affineRoundMiddleLeft h t L e l wl)
    (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1) (fun z => x z.1.1.1.1)
    (affineRoundFinalSeedRight d t L e ys) (affineRoundMiddleLeftEnvelope d h t L e μ r wr ys)
    (fun z => (hr₃ z).1)
    (affineRoundMiddle_left_envelope d h t L e w l r wl wr ys x μ hw hl hr cap) z x₀

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
      affineRoundTranscriptRightEnvelope h t L e ξ l wl z := by
  obtain ⟨hw₃, _, hr₃⟩ := affineRoundMiddle_probability d h t L e w l r wl wr ys hw hl hr
  exact observedTranscript_left_envelope (affineRoundMiddleWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1) (fun z => y z.1.1.1.1)
    (affineRoundFinalSeedRight d t L e ys) (affineRoundMiddleRightEnvelope h t L e ξ l wl)
    hw₃.1 (fun z => (hr₃ z).1)
    (affineRoundMiddle_right_envelope d h t L e w l r wl wr ys y ξ hw hl hr cap) z y₀

end Algebraic.Cutwidth.Extractor.Internal
