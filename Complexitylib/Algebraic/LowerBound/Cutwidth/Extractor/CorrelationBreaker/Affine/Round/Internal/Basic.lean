/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Transcript.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched

/-!
# Exact side-local equations for the actual affine round

False-completed prefixes respect XOR. The matched extractors' checked
linearity then makes the actual short row left-only after its right seed
and mask have been observed, and splits the next long row into its original
left and right contributions. No extractor security theorem is used.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundPrefix_xor (h L : Nat)
    (left right : Fin (matchedBlockOutputBits h L) → Bool) :
    affineRoundPrefix h L (fun j => Bool.xor (left j) (right j)) =
      fun j => Bool.xor (affineRoundPrefix h L left j) (affineRoundPrefix h L right j) := by
  funext j
  by_cases inside : j.val < matchedBlockOutputBits h L
  · simp only [affineRoundPrefix, List.getElem?_ofFn, dite_eq_left inside, Option.getD_some]
  · simp only [affineRoundPrefix, List.getElem?_ofFn, dite_eq_right inside, Option.getD_none,
      Bool.false_xor]

theorem affineRoundPrefixLeftMessage_eq (h t L : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (p : (Z × B) × A) :
    affineRoundPrefixLeftMessage h t L wl (affineRoundPrefixMaskTranscript h t L wr p.1) p.2 =
      fun i => affineRoundPrefix h L
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) := by
  funext i
  dsimp only [affineRoundPrefixLeftMessage, affineRoundPrefixMaskTranscript,
    affineRoundPrefixMask]
  exact (affineRoundPrefix_xor h L _ _).symm

theorem affineRoundMiddleSeedRight_eq (d h t L e : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affineRoundMiddleSeedRight d t L e ys (affineRoundPrefixTranscript h t L wl wr p) p.1.2 =
      fun i => affineRoundMiddleSeed d h L e (ys p.1.1 p.1.2 i)
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) := by
  unfold affineRoundMiddleSeedRight affineRoundMiddleSeed
  dsimp only [affineRoundPrefixTranscript, affineRoundPrefixMaskTranscript]

theorem affineRoundMiddleLeftMessage_eq (d h t L e : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affineRoundMiddleLeftMessage h t L e wl
        (affineRoundMiddleRightTranscript d h t L e wl wr ys p) p.2 =
      fun i => affineRoundMiddleOutput d h L e (ys p.1.1 p.1.2 i)
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) := by
  funext i
  unfold affineRoundMiddleLeftMessage
  dsimp only [affineRoundMiddleRightTranscript, affineRoundMiddleRightMessage]
  simp only [affineRoundMiddleSeedRight_eq]
  dsimp only [affineRoundPrefixTranscript, affineRoundPrefixMaskTranscript]
  unfold affineRoundMiddleOutput
  exact (matchedBlockExtractor_xor (matchedBlockOutputBits h L) 24 L e
    (wl p.1.1 p.2 i) (wr p.1.1 p.1.2 i) _).symm

theorem affineRoundFinalSeedRight_eq (d h t L e : Nat) {Z A B : Type*}
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affineRoundFinalSeedRight d t L e ys
        (affineRoundMiddleTranscript d h t L e wl wr ys p) p.1.2 =
      fun i => affineRoundFinalSeed d h L e (ys p.1.1 p.1.2 i)
        (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j)) := by
  unfold affineRoundFinalSeedRight affineRoundFinalSeed
  dsimp only [affineRoundMiddleTranscript,
    affineRoundMiddleRightTranscript, affineRoundPrefixTranscript,
    affineRoundPrefixMaskTranscript]

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
          (affineRoundTranscript d h t L e wl wr ys p) p.1.2 i j) := by
  dsimp only [affineRoundOutput, affineRoundOutputLeft, affineRoundOutputRight,
    affineRoundTranscript, affineRoundMiddleTranscript, affineRoundMiddleRightTranscript,
    affineRoundPrefixTranscript, affineRoundPrefixMaskTranscript]
  exact matchedBlockExtractor_xor n h L e (x p.1.1 p.2) (mask p.1.1 p.1.2) _

end Algebraic.Cutwidth.Extractor.Internal
