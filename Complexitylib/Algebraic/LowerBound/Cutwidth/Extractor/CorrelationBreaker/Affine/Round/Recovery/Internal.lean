/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Middle.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Copies
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched

/-!
# Recover the final seed by rereading the original right source

The actual short row supplies the next seed. The complete right-state
kernel already records prefix masks, first right seeds, and middle masks,
so the original right envelope pays three short-message alphabets. The
alternating extraction observes every actual short row without an extra
right-source cost.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundFinalSeed_dist_le (d h t L e : Nat)
    (length : Nat.clog 2 (d + 1) ≤ L) (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) (ν : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ ν z)
    (cap : ∀ z y₀, w z * mapWeight (fun b => ys z b none) (r z) y₀ ≤ ν z)
    (seed : weightDist (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundMiddleSeedInputWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)) ≤
        ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ 62 * L) *
          (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 3 * ∑ z, ν z := by
  have normalized := affineRoundMiddleRight_probability d h t L e w l r wl wr ys hw hl hr
  have cap' := affineRoundMiddleRight_right_envelope d h t L e w l r wl wr ys
    (fun z b => ys z b none) ν hw hl hr cap
  have bound := (matchedBlockExtractor_depth24 d L e length room error).alternating_copies_dist_le
    (by positivity) (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundPrefixLeft h t L l wl z.1)
    (affineRoundMiddleRightKernel d h t L e r wr ys) (affineRoundMiddleLeftMessage h t L e wl)
    (fun z => ys z.1.1.1) S (affineRoundMiddleRightRightEnvelope h t L ν l wl)
    normalized.1 normalized.2.1 normalized.2.2
    (affineRoundMiddleRightRightEnvelope_nonnegative h t L ν l wl nonnegative
      (fun z => (hl z).1)) cap' seed
  rw [alternatingCopiesWeight_eq_observed
    (affineRoundMiddleRightWeight d h t L e w l r wl wr ys)
    (fun z => affineRoundPrefixLeft h t L l wl z.1)
    (affineRoundMiddleRightKernel d h t L e r wr ys) (affineRoundMiddleLeftMessage h t L e wl)
    (fun z => ys z.1.1.1) (matchedBlockExtractor d 24 L e) S normalized.2.1] at bound
  change weightDist (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)
    (uniformSecondWeight (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)) ≤ _ at bound
  rw [affineRoundMiddleRightRightEnvelope_sum h t L ν l wl (fun z => (hl z).2)] at bound
  have cards : Fintype.card (Fin (matchedBlockOutputBits 24 L) → Bool) =
      Fintype.card (Fin (matchedBlockSeedBits L) → Bool) :=
    Fintype.card_congr (Equiv.refl _)
  convert bound using 1
  rw [cards]
  simp only [Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

end Algebraic.Cutwidth.Extractor.Internal
