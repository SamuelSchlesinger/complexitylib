/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Internal.Left
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Internal.Mask
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Composing middle-left extraction, masking, and the next seed law

The source and seed discrepancies refer only to actual original laws.
Masking and transcript projection add no error to the smooth merging bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundMiddleSeedInputWeight_probability (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (U : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys U) := by
  rw [← affineRoundMiddleSeedInputWeight_eq_map d h t L e w l r wl wr ys U hl hr]
  exact (affineRoundMiddleRowsWeight_probability d h t L e w l r wl wr ys U hw hl hr).map _

theorem affineRound_middle_dist_le (d h t L e : Nat) {Z A B : Type*}
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
    weightDist (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys (S ∪ T))
      (uniformSecondWeight
        (affineRoundMiddleRowsWeight d h t L e w l r wl wr ys (S ∪ T))) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + ρ + (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          Fintype.card (AffineRoundShortMessages t L) /
            Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) :=
  (affineRound_middle_mask_dist_le d h t L e w l r wl wr ys (S ∪ T)).trans
    (affineRound_middle_left_dist_le d h t L e w l r wl wr ys S T
      length room error hw hl hr source seed)

theorem affineRound_middle_seed_input_dist_le (d h t L e : Nat) {Z A B : Type*}
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
    weightDist (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys (S ∪ T))
      (uniformSecondWeight
        (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys (S ∪ T))) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + ρ + (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          Fintype.card (AffineRoundShortMessages t L) /
            Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) :=
  (affineRound_middle_seed_input_projection_dist_le d h t L e w l r wl wr ys (S ∪ T)
    hl hr).trans (affineRound_middle_dist_le d h t L e w l r wl wr ys S T
      length room error hw hl hr source seed)

end Algebraic.Cutwidth.Extractor.Internal
