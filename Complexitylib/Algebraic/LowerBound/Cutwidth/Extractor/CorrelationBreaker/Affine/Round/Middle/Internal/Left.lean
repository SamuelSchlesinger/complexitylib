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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Independence
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Distance
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched

/-!
# Smooth-source merging for the actual middle-left extraction

The first right observation preserves the old averaged source error.
Smooth independence merging then applies to the actual prefix family.
All middle-right messages are reconstructed from the retained prefix and
original right state, so restoring that complete transcript costs no error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def affineRoundMiddleRetained (d h t L e : Nat) {Z B : Type*}
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (p : (AffineRoundPrefixTranscript Z t L × B) ×
      (U → Fin (matchedBlockSeedBits L) → Bool)) :=
  (((p.1.1, affineRoundMiddleRightMessage d h t L e wr ys p.1.1 p.1.2), p.1.2), p.2)

private theorem affineRoundMiddleLeftRowsWeight_eq_map_smooth (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t))
    (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p => (affineRoundMiddleRetained d h t L e wr ys (S ∪ T) p.1, p.2))
      (smoothIndependenceMergingWeight (Out := Fin (matchedBlockSeedBits L) → Bool)
        (affineRoundPrefixMaskWeight h t L w r wr)
        (fun z => l z.1) (affineRoundPrefixMaskRight h t L r wr)
        (fun z a => wl z.1 a) (affineRoundPrefixLeftMessage h t L wl)
        (affineRoundMiddleSeedRight d t L e ys)
        (matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e) S T) =
      affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys (S ∪ T) := by
  unfold smoothIndependenceMergingWeight
  rw [← affineRoundPrefixMask_factored h t L w l r wr hr, mapWeight_comp, mapWeight_comp]
  unfold affineRoundMiddleLeftRowsWeight
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [affineRoundPrefixLeftMessage_eq]
  dsimp only [affineRoundMiddleRetained, affineRoundMiddleRightTranscript,
    affineRoundPrefixTranscript, affineRoundMiddleRightMessage, affineRoundPrefixMaskTranscript]

theorem affineRoundMiddleLeftRowsWeight_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys U) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem affineRound_middle_left_dist_le (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S T : Finset (Fin t)) {ρ δ : ℝ}
    (length : Nat.clog 2 (matchedBlockOutputBits h L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (affineRoundLeftRowsWeight h t L w l wl T)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl T)) ≤ ρ)
    (seed : weightDist (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys (S ∪ T))
      (uniformSecondWeight
        (affineRoundMiddleLeftRowsWeight d h t L e w l r wl wr ys (S ∪ T))) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + ρ + (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          Fintype.card (AffineRoundShortMessages t L) /
            Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) := by
  have original : weightDist
      (smoothIndependenceSourceWeight (affineRoundPrefixMaskWeight h t L w r wr)
        (fun z => l z.1) (fun z a => wl z.1 a) T)
      (uniformSecondWeight
        (smoothIndependenceSourceWeight (affineRoundPrefixMaskWeight h t L w r wr)
          (fun z => l z.1) (fun z a => wl z.1 a) T)) ≤ ρ := by
    unfold smoothIndependenceSourceWeight affineRoundPrefixMaskWeight
    rw [observedSeedWeight_observe_other_dist w l r (affineRoundPrefixMask h t L wr)
      (fun z a (j : T) => wl z a (some j)) (fun z a => wl z a none) hw.1 hr]
    exact source
  obtain ⟨hw₀, hr₀⟩ := affineRoundPrefixMask_probability h t L w r wr hw hr
  have extract : WeightedStrongSeededExtractor
      (Ω := Fin (matchedBlockSeedBits L) → Bool)
      (matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e)
      (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) := by
    convert matchedBlockExtractor_depth24 (matchedBlockOutputBits h L) L e
      length room error using 1
    rfl
  have merged := extract.smooth_independence_merging_dist_le (by positivity)
    (affineRoundPrefixMaskWeight h t L w r wr) (fun z => l z.1)
    (affineRoundPrefixMaskRight h t L r wr) (fun z a => wl z.1 a)
    (affineRoundPrefixLeftMessage h t L wl) (affineRoundMiddleSeedRight d t L e ys)
    S T hw₀ (fun z => hl z.1) hr₀ original seed
  have projected := weightDist_uniformSecond_map_first_le
    (smoothIndependenceMergingWeight (Out := Fin (matchedBlockSeedBits L) → Bool)
        (affineRoundPrefixMaskWeight h t L w r wr)
      (fun z => l z.1) (affineRoundPrefixMaskRight h t L r wr)
      (fun z a => wl z.1 a) (affineRoundPrefixLeftMessage h t L wl)
      (affineRoundMiddleSeedRight d t L e ys)
      (matchedBlockExtractor (matchedBlockOutputBits h L) 24 L e) S T)
    (affineRoundMiddleRetained d h t L e wr ys (S ∪ T))
  rw [affineRoundMiddleLeftRowsWeight_eq_map_smooth d h t L e w l r wl wr ys S T
    (fun z => (hr z).1)] at projected
  exact projected.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using merged)

end Algebraic.Cutwidth.Extractor.Internal
