/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Internal.Extraction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Internal.Mask
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing
import Mathlib.Tactic.Positivity

/-!
# Actual final extraction from the original left source

The checked observation envelope pays for both left short-message vectors.
Instantiating the subset leakage bound with the actual growing matched
extractor gives the final-call estimate. Masking costs no additional error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundLeftSubset_dist_le (n d h t L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
      (uniformSecondWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L) *
        (Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) : ℝ) ^ S.card *
        (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z := by
  have bound := affineRoundLeftSubset_dist_le_of_middleEnvelope n d h t L e _
    (matchedBlockExtractor_growing n h L e length error budget) (by positivity)
    w l r x wl wr ys S (affineRoundMiddleLeftEnvelope d h t L e μ r wr ys)
    hw hl hr (affineRoundMiddleLeftEnvelope_nonnegative d h t L e μ r wr ys nonnegative hr)
    (affineRoundMiddle_left_envelope d h t L e w l r wl wr ys x μ hw hl hr cap) seed
  rw [affineRoundMiddleLeftEnvelope_sum d h t L e μ r wr ys hr] at bound
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using bound

theorem affineRoundSubset_dist_le (n d h t L e : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L) (error : e + h + 2 ≤ L)
    (budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) (μ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)
      (uniformSecondWeight (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)) ≤
      ((2 : ℝ) ^ e)⁻¹ + δ + (2 : ℝ) ^ (2 ^ (2 * h + 14) * L) *
        (Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) : ℝ) ^ S.card *
        (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 2 * ∑ z, μ z :=
  (affineRoundSubset_dist_le_left n d h t L e w l r x mask wl wr ys S).trans
    (affineRoundLeftSubset_dist_le n d h t L e length error budget
      w l r x wl wr ys S μ hw hl hr nonnegative cap seed)

end Algebraic.Cutwidth.Extractor.Internal
