/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Basic

/-!
# Transport from left contributions to actual short rows

The complete retained middle-right transcript supplies every XOR mask.
Masking the honest output is a fibrewise bijection, and masking the retained
tampered rows is deterministic postprocessing. Dropping the original right
state then gives precisely the observed seed-input law for the next call.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def middleXorEquiv {ι : Type*} (mask : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x i := Bool.xor (x i) (mask i)
  invFun x i := Bool.xor (x i) (mask i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

private def middleMaskedTag {Z B : Type*} {t L : Nat} (U : Finset (Fin t))
    (p : (AffineRoundMiddleRightTranscript Z t L × B) ×
      (U → Fin (matchedBlockSeedBits L) → Bool)) :=
  (p.1, fun (j : U) i => Bool.xor (p.2 j i) (p.1.1.2.2 (some j) i))

private theorem affineRoundMiddleRowsWeight_eq_mask (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t)) :
    mapWeight (fun p => (middleMaskedTag U p.1,
      middleXorEquiv (p.1.1.1.2.2 none) p.2))
      (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U) =
      affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U := by
  unfold affineRoundMiddleLeftRowsWeight affineRoundMiddleRowsWeight
  rw [mapWeight_comp]
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  have actual := congrArg
    (fun f : Option (Fin t) → Fin (matchedBlockSeedBits L) → Bool =>
      (((affineRoundMiddleRightTranscript d h t L e wl wr ys p, p.1.2),
        fun j : U => f (some j)), f none))
    (affineRoundMiddleLeftMessage_eq d h t L e wl wr ys p)
  dsimp only [affineRoundMiddleLeftMessage, affineRoundMiddleRightTranscript,
    affineRoundPrefixTranscript, affineRoundPrefixMaskTranscript] at actual
  dsimp only [Function.comp_apply, middleMaskedTag, middleXorEquiv, Equiv.coe_fn_mk,
    affineRoundMiddleRightTranscript, affineRoundPrefixTranscript,
    affineRoundPrefixMaskTranscript]
  exact actual

theorem affineRound_middle_mask_dist_le (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t)) :
    weightDist (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U)
      (uniformSecondWeight (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U)) ≤
      weightDist (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U)
        (uniformSecondWeight (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U)) := by
  let law := affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U
  let twist : ((AffineRoundMiddleRightTranscript Z t L × B) ×
      (U → Fin (matchedBlockSeedBits L) → Bool)) →
      (Fin (matchedBlockSeedBits L) → Bool) ≃ (Fin (matchedBlockSeedBits L) → Bool) :=
    fun p => middleXorEquiv (p.1.1.2.2 none)
  have output := weightDist_uniformSecond_fiberEquiv law twist
  have tag := weightDist_uniformSecond_map_first_le
    (mapWeight (fun p => (p.1, twist p.1 p.2)) law) (middleMaskedTag U)
  have transformed := tag.trans_eq output
  simp only [mapWeight_comp, law, twist] at transformed
  rw [affineRoundMiddleRowsWeight_eq_mask d h t L e w l r wl wr ys U] at transformed
  exact transformed

theorem affineRoundMiddleRowsWeight_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem affineRoundMiddleSeedInputWeight_eq_map (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p => ((p.1.1.1, p.1.2), p.2))
      (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U) =
      affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys U := by
  unfold affineRoundMiddleSeedInputWeight
  have hr₂ : ∀ z, IsProbabilityWeight (affineRoundMiddleRightKernel d h t L e r wr ys z) := by
    apply observedTranscriptKernel_probability
    intro z
    exact observedTranscriptKernel_probability r _ hr z.1
  rw [smooth_observedSeedWeight_eq_factored _ _ _ _ _ hr₂,
    ← factoredWeight_swap,
    ← affineRoundMiddleRight_factored d h t L e w l r wl wr ys (fun z => (hl z).1) hr,
    mapWeight_comp]
  unfold affineRoundMiddleRowsWeight
  rw [mapWeight_comp, mapWeight_comp]
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [affineRoundMiddleLeftMessage_eq]

theorem affineRound_middle_seed_input_projection_dist_le (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys U)
      (uniformSecondWeight (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys U)) ≤
      weightDist (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U)
        (uniformSecondWeight (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U)) := by
  have bound := weightDist_uniformSecond_map_first_le
    (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys U) (fun p => (p.1.1, p.2))
  rw [affineRoundMiddleSeedInputWeight_eq_map d h t L e w l r wl wr ys U hl hr] at bound
  exact bound

end Algebraic.Cutwidth.Extractor.Internal
