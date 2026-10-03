/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Transcript.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Internal.Factorization

/-!
# Exact execution factors of one affine extraction round

The four actual matched calls follow the second-phase construction of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Theorem 6.1,
printed pp.23--25: <https://arxiv.org/abs/2110.12652>. The full transcript
records right prefix masks, actual prefixes, middle seeds and mask outputs,
actual short outputs, and final right seeds in their execution order.

The law is exactly the original factored law with these observations added.
Both original latent states are retained, and every conditional kernel is
normalized, including impossible messages. These algebraic and probability
identities use no statistical guarantee for any component extractor.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- False-completed prefixes commute with pointwise XOR at every row width. -/
theorem affineRoundPrefix_xor (h L : Nat)
    (left right : Fin (matchedBlockOutputBits h L) → Bool) :
    affineRoundPrefix h L (fun j => Bool.xor (left j) (right j)) =
      fun j => Bool.xor (affineRoundPrefix h L left j) (affineRoundPrefix h L right j) :=
  Internal.affineRoundPrefix_xor h L left right

/-- The left prefix message is exactly the prefix of each actual masked previous row. -/
theorem affineRoundPrefixLeftMessage_eq (h t L : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (p : (Z × B) × A) :
    affineRoundPrefixLeftMessage h t L wl (affineRoundPrefixMaskTranscript h t L wr p.1) p.2 =
      fun i => affineRoundPrefix h L
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) :=
  Internal.affineRoundPrefixLeftMessage_eq h t L wl wr p

/-- The right-only middle seed is the actual first right extraction. -/
theorem affineRoundMiddleSeedRight_eq (d h t L e : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affineRoundMiddleSeedRight d t L e ys (affineRoundPrefixTranscript h t L wl wr p) p.1.2 =
      fun i => affineRoundMiddleSeed d h L e (ys p.1.1 p.1.2 i)
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) :=
  Internal.affineRoundMiddleSeedRight_eq d h t L e wl wr ys p

/-- The left middle message is exactly the actual short extraction output. -/
theorem affineRoundMiddleLeftMessage_eq (d h t L e : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affineRoundMiddleLeftMessage h t L e wl
        (affineRoundMiddleRightTranscript d h t L e wl wr ys p) p.2 =
      fun i => affineRoundMiddleOutput d h L e (ys p.1.1 p.1.2 i)
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) :=
  Internal.affineRoundMiddleLeftMessage_eq d h t L e wl wr ys p

/-- The right-only final seed is the actual second right extraction. -/
theorem affineRoundFinalSeedRight_eq (d h t L e : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affineRoundFinalSeedRight d t L e ys
        (affineRoundMiddleTranscript d h t L e wl wr ys p) p.1.2 =
      fun i => affineRoundFinalSeed d h L e (ys p.1.1 p.1.2 i)
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) :=
  Internal.affineRoundFinalSeedRight_eq d h t L e wl wr ys p

/-- Every actual next row is the XOR of its original-left and original-right contributions. -/
theorem affineRoundOutput_eq_xor (n d h t L e : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) (i : Option (Fin t)) :
    affineRoundOutput n d h L e
        (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j)) (ys p.1.1 p.1.2 i)
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) =
      fun j => Bool.xor
        (affineRoundOutputLeft n h t L e x
          (affineRoundTranscript d h t L e wl wr ys p) p.2 i j)
        (affineRoundOutputRight n h t L e mask
          (affineRoundTranscript d h t L e wl wr ys p) p.1.2 i j) :=
  Internal.affineRoundOutput_eq_xor n d h t L e x mask wl wr ys p i

/-- The first right observation has normalized transcript and right kernels. -/
theorem affineRoundPrefixMask_probability (h t L : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hw : IsProbabilityWeight w) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundPrefixMaskWeight h t L w r wr) ∧
      ∀ z, IsProbabilityWeight (affineRoundPrefixMaskRight h t L r wr z) :=
  Internal.affineRoundPrefixMask_probability h t L w r wr hw hr

/-- After actual prefixes, the transcript and both original-state kernels are normalized. -/
theorem affineRoundPrefix_probability (h t L : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundPrefixWeight h t L w l r wl wr) ∧
      (∀ z, IsProbabilityWeight (affineRoundPrefixLeft h t L l wl z)) ∧
      ∀ z, IsProbabilityWeight (affineRoundPrefixRight h t L r wr z) :=
  Internal.affineRoundPrefix_probability h t L w l r wl wr hw hl hr

/-- Observing the first right seeds and short-row masks preserves normalization. -/
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
      ∀ z, IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z) :=
  Internal.affineRoundMiddleRight_probability d h t L e w l r wl wr ys hw hl hr

/-- After actual short rows, every conditional kernel remains normalized, including null rows. -/
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
        IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z.1) :=
  Internal.affineRoundMiddle_probability d h t L e w l r wl wr ys hw hl hr

/-- The full actual transcript and both original-state kernels are normalized. -/
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
      ∀ z, IsProbabilityWeight (affineRoundTranscriptRight d h t L e r wr ys z) :=
  Internal.affineRoundTranscript_probability d h t L e w l r wl wr ys hw hl hr

/-- Observing right prefix masks preserves the complete original factored law exactly. -/
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
  Internal.affineRoundPrefixMask_factored h t L w l r wr hr

/-- The actual prefix transcript has exactly the displayed original-state factorization. -/
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
        (affineRoundPrefixLeft h t L l wl) (affineRoundPrefixRight h t L r wr) :=
  Internal.affineRoundPrefix_factored h t L w l r wl wr hl hr

/-- The right seeds and short-row masks extend the exact actual factorization. -/
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
        (affineRoundMiddleRightKernel d h t L e r wr ys) :=
  Internal.affineRoundMiddleRight_factored d h t L e w l r wl wr ys hl hr

/-- The actual short rows extend the exact actual factorization. -/
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
        (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1) :=
  Internal.affineRoundMiddle_factored d h t L e w l r wl wr ys hl hr

/-- The entire executed round transcript has the displayed exact original-state factorization. -/
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
        (affineRoundTranscriptLeft h t L e l wl) (affineRoundTranscriptRight d h t L e r wr ys) :=
  Internal.affineRoundTranscript_factored d h t L e w l r wl wr ys hl hr

end Algebraic.Cutwidth.Extractor
