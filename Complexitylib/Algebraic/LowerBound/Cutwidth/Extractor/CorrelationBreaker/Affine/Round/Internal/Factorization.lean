/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Transcript.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript

/-!
# Normalization and exact factorization of the executed affine round

Five deterministic observations preserve the complete original law. Their
alternating conditional kernels are normalized at every transcript, even
when the message has zero probability. Linearity is used only to identify
the two left observations with the actual executed prefix and short row.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundPrefixMask_probability (h t L : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hw : IsProbabilityWeight w) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundPrefixMaskWeight h t L w r wr) ∧
      ∀ z, IsProbabilityWeight (affineRoundPrefixMaskRight h t L r wr z) :=
  ⟨observedTranscriptWeight_probability _ _ _ hw hr,
    observedTranscriptKernel_probability _ _ hr⟩

theorem affineRoundPrefix_probability (h t L : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundPrefixWeight h t L w l r wl wr) ∧
      (∀ z, IsProbabilityWeight (affineRoundPrefixLeft h t L l wl z)) ∧
      ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) := by
  obtain ⟨hw₀, hr₀⟩ := affineRoundPrefixMask_probability h t L w r wr hw hr
  exact ⟨observedTranscriptWeight_probability _ _ _ hw₀ (fun z => hl z.1),
    observedTranscriptKernel_probability _ _ (fun z => hl z.1), fun z => hr₀ z.1⟩

theorem affineRoundMiddleRight_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleRightWeight d h t L e w l r wl wr ys) ∧
      (∀ z : AffineRoundMiddleRightTranscript Z t L,
        IsProbabilityWeight (affineRoundPrefixLeft h t L l wl z.1)) ∧
      ∀ z, IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z) := by
  obtain ⟨hw₁, hl₁, hr₁⟩ := affineRoundPrefix_probability h t L w l r wl wr hw hl hr
  exact ⟨observedTranscriptWeight_probability _ _ _ hw₁ hr₁,
    fun z => hl₁ z.1, observedTranscriptKernel_probability _ _ hr₁⟩

theorem affineRoundMiddle_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleWeight d h t L e w l r wl wr ys) ∧
      (∀ z, IsProbabilityWeight (affineRoundMiddleLeft h t L e l wl z)) ∧
      ∀ z : AffineRoundMiddleTranscript Z t L,
        IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z.1) := by
  obtain ⟨hw₂, hl₂, hr₂⟩ :=
    affineRoundMiddleRight_probability d h t L e w l r wl wr ys hw hl hr
  exact ⟨observedTranscriptWeight_probability _ _ _ hw₂ hl₂,
    observedTranscriptKernel_probability _ _ hl₂, fun z => hr₂ z.1⟩

theorem affineRoundTranscript_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundTranscriptWeight d h t L e w l r wl wr ys) ∧
      (∀ z, IsProbabilityWeight (affineRoundTranscriptLeft h t L e l wl z)) ∧
      ∀ z, IsProbabilityWeight (affineRoundTranscriptRight d h t L e r wr ys z) := by
  obtain ⟨hw₃, hl₃, hr₃⟩ := affineRoundMiddle_probability d h t L e w l r wl wr ys hw hl hr
  exact ⟨observedTranscriptWeight_probability _ _ _ hw₃ hr₃,
    fun z => hl₃ z.1, observedTranscriptKernel_probability _ _ hr₃⟩

theorem affineRoundPrefixMask_factored (h t L : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((affineRoundPrefixMaskTranscript h t L wr p.1, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affineRoundPrefixMaskWeight h t L w r wr)
        (fun z => l z.1) (affineRoundPrefixMaskRight h t L r wr) :=
  factoredWeight_observe_right w l r _ hr

theorem affineRoundPrefix_factored (h t L : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((affineRoundPrefixTranscript h t L wl wr p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affineRoundPrefixWeight h t L w l r wl wr)
        (affineRoundPrefixLeft h t L l wl) (affineRoundPrefixRight h t L r wr) := by
  have first := affineRoundPrefixMask_factored h t L w l r wr hr
  have second := factoredWeight_observe_left (affineRoundPrefixMaskWeight h t L w r wr)
    (fun z => l z.1) (affineRoundPrefixMaskRight h t L r wr)
    (affineRoundPrefixLeftMessage h t L wl) (fun z => hl z.1)
  rw [← first, mapWeight_comp] at second
  unfold affineRoundPrefixWeight affineRoundPrefixLeft affineRoundPrefixRight
  rw [← second]
  apply congrArg (fun f : (Z × B) × A → (AffineRoundPrefixTranscript Z t L × B) × A =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [affineRoundPrefixLeftMessage_eq]
  rfl

theorem affineRoundMiddleRight_factored (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((affineRoundMiddleRightTranscript d h t L e wl wr ys p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
        (fun z => affineRoundPrefixLeft h t L l wl z.1)
        (affineRoundMiddleRightKernel d h t L e r wr ys) := by
  have first := affineRoundPrefix_factored h t L w l r wl wr hl (fun z => (hr z).1)
  have hr₀ : ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) :=
    fun z => observedTranscriptKernel_probability r _ hr z.1
  have second := factoredWeight_observe_right (affineRoundPrefixWeight h t L w l r wl wr)
    (affineRoundPrefixLeft h t L l wl) (affineRoundPrefixRight h t L r wr)
    (affineRoundMiddleRightMessage d h t L e wr ys) (fun z => (hr₀ z).1)
  rw [← first, mapWeight_comp] at second
  exact second

theorem affineRoundMiddle_factored (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((affineRoundMiddleTranscript d h t L e wl wr ys p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affineRoundMiddleWeight d h t L e w l r wl wr ys)
        (affineRoundMiddleLeft h t L e l wl)
        (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1) := by
  have first := affineRoundMiddleRight_factored d h t L e w l r wl wr ys
    (fun z => (hl z).1) hr
  have hl₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixLeft h t L l wl z) :=
    observedTranscriptKernel_probability _ _ (fun z => hl z.1)
  have second := factoredWeight_observe_left
    (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundPrefixLeft h t L l wl z.1)
    (affineRoundMiddleRightKernel d h t L e r wr ys)
    (affineRoundMiddleLeftMessage h t L e wl) (fun z => (hl₁ z.1).1)
  rw [← first, mapWeight_comp] at second
  unfold affineRoundMiddleWeight affineRoundMiddleLeft
  rw [← second]
  apply congrArg (fun f : (Z × B) × A → (AffineRoundMiddleTranscript Z t L × B) × A =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [affineRoundMiddleLeftMessage_eq]
  rfl

theorem affineRoundTranscript_factored (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((affineRoundTranscript d h t L e wl wr ys p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
        (affineRoundTranscriptLeft h t L e l wl) (affineRoundTranscriptRight d h t L e r wr ys) := by
  have first := affineRoundMiddle_factored d h t L e w l r wl wr ys hl hr
  have hr₁ : ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) :=
    fun z => observedTranscriptKernel_probability r _ hr z.1
  have hr₂ : ∀ z, IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z) :=
    observedTranscriptKernel_probability _ _ hr₁
  have second := factoredWeight_observe_right
    (affineRoundMiddleWeight d h t L e w l r wl wr ys)
    (affineRoundMiddleLeft h t L e l wl)
    (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
    (affineRoundFinalSeedRight d t L e ys) (fun z => (hr₂ z.1).1)
  rw [← first, mapWeight_comp] at second
  unfold affineRoundTranscriptWeight affineRoundTranscriptLeft affineRoundTranscriptRight
  rw [← second]
  apply congrArg (fun f : (Z × B) × A → (AffineRoundTranscript Z t L × B) × A =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [affineRoundFinalSeedRight_eq]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
