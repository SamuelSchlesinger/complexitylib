/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Distance
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Copies
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation

/-!
# A retained subset supplies the actual masked prefix seed

The balanced prefix contracts the old row discrepancy. Observing the
independent right masks preserves its average exactly, and the transcript
then determines the XOR masks on the honest and selected tampered prefixes.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundLeftRowsWeight_probability (h t L : Nat)
    {Z A : Type*} [Fintype Z] [Fintype A] (w : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z)) :
    IsProbabilityWeight (affineRoundLeftRowsWeight h t L w l wl S) :=
  observedSeedWeight_probability w l _ _ hw hl

theorem affineRoundPrefixSeedWeight_probability (h t L : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundPrefixSeedWeight h t L w l r wl wr S) :=
  observedSeedWeight_probability _ _ _ _
    (affineRoundPrefixMask_probability h t L w r wr hw hr).1 (fun z => hl z.1)

theorem affineRoundMiddleSeedWeight_probability (d h t L e : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S) := by
  have normalized := affineRoundPrefix_probability h t L w l r wl wr hw hl hr
  exact observedSeedWeight_probability _ _ _ _ normalized.1 normalized.2.2

private def roundXorEquiv {ι : Type*} (mask : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x i := Bool.xor (x i) (mask i)
  invFun x i := Bool.xor (x i) (mask i)
  left_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl
  right_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl

theorem affineRoundPrefix_uniform (h L : Nat)
    (size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L) :
    mapWeight (affineRoundPrefix h L)
      (uniformWeight (Fin (matchedBlockOutputBits h L) → Bool)) =
        uniformWeight (Fin (matchedBlockSeedBits L) → Bool) :=
  adviceOutputPrefix_uniform size

theorem affineRoundPrefixSeed_dist_le (h t L : Nat)
    (size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (S : Finset (Fin t))
    (hw : ∀ z, 0 ≤ w z) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (affineRoundPrefixSeedWeight h t L w l r wl wr S)
      (uniformSecondWeight (affineRoundPrefixSeedWeight h t L w l r wl wr S)) ≤
        weightDist (affineRoundLeftRowsWeight h t L w l wl S)
          (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl S)) := by
  have image := observedSeedWeight_image_dist_le w l
    (fun z a (j : S) => wl z a (some j)) (fun z a => wl z a none)
    (affineRoundPrefix h L) (affineRoundPrefix_uniform h L size)
  have observed := observedSeedWeight_observe_other_dist w l r
    (affineRoundPrefixMask h t L wr) (fun z a (j : S) => wl z a (some j))
    (fun z a => affineRoundPrefix h L (wl z a none)) hw hr
  have masked := observedSeedWeight_transform_dist_le
    (affineRoundPrefixMaskWeight h t L w r wr) (fun z => l z.1)
    (fun z a (j : S) => wl z.1 a (some j))
    (fun z a => affineRoundPrefix h L (wl z.1 a none))
    (fun z rows (j : S) k => Bool.xor (affineRoundPrefix h L (rows j) k) (z.2 (some j) k))
    (fun z => roundXorEquiv (z.2 none))
  change weightDist (affineRoundPrefixSeedWeight h t L w l r wl wr S)
    (uniformSecondWeight (affineRoundPrefixSeedWeight h t L w l r wl wr S)) ≤ _ at masked
  exact masked.trans (observed.le.trans image)

theorem affineRoundMiddleSeed_dist_le (d h t L e : Nat)
    (size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L)
    (length : Nat.clog 2 (d + 1) ≤ L) (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) (ν : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ ν z)
    (cap : ∀ z y₀, w z * mapWeight (fun b => ys z b none) (r z) y₀ ≤ ν z)
    (old : weightDist (affineRoundLeftRowsWeight h t L w l wl S)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl S)) ≤ ρ) :
    weightDist (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)) ≤
        ((2 : ℝ) ^ e)⁻¹ + ρ + (2 : ℝ) ^ (2 ^ 62 * L) *
          (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ S.card *
          Fintype.card (AffineRoundShortMessages t L) * ∑ z, ν z := by
  have near := (affineRoundPrefixSeed_dist_le h t L size w l r wl wr S hw.1 hr).trans old
  have cap' (z : AffineRoundPrefixMaskTranscript Z t L) (y₀ : Fin d → Bool) :
      affineRoundPrefixMaskWeight h t L w r wr z *
        mapWeight (fun b => ys z.1 b none) (affineRoundPrefixMaskRight h t L r wr z) y₀ ≤
          ν z.1 :=
    observedTranscript_left_envelope w r (fun z b => ys z b none)
      (affineRoundPrefixMask h t L wr) ν hw.1 (fun z => (hr z).1) cap z y₀
  have bound := (matchedBlockExtractor_depth24 d L e length room error).alternating_copies_dist_le
    (by positivity) (affineRoundPrefixMaskWeight h t L w r wr) (fun z => l z.1)
    (affineRoundPrefixMaskRight h t L r wr) (affineRoundPrefixLeftMessage h t L wl)
    (fun z => ys z.1) S (fun z => ν z.1)
    (observedTranscriptWeight_probability w r (affineRoundPrefixMask h t L wr) hw hr)
    (fun z => hl z.1) (observedTranscriptKernel_probability r (affineRoundPrefixMask h t L wr) hr)
    (fun z => nonnegative z.1) cap' near
  rw [alternatingCopiesWeight_eq_observed (affineRoundPrefixMaskWeight h t L w r wr)
    (fun z => l z.1) (affineRoundPrefixMaskRight h t L r wr)
    (affineRoundPrefixLeftMessage h t L wl) (fun z => ys z.1)
    (matchedBlockExtractor d 24 L e) S (fun z => hl z.1)] at bound
  change weightDist (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)
    (uniformSecondWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S)) ≤ _ at bound
  rw [observedTranscript_left_envelope_sum ν] at bound
  have cards : Fintype.card (Fin (matchedBlockOutputBits 24 L) → Bool) =
      Fintype.card (Fin (matchedBlockSeedBits L) → Bool) :=
    Fintype.card_congr (Equiv.refl _)
  convert bound using 1
  rw [cards]
  simp only [Nat.cast_pow, Nat.cast_ofNat, mul_assoc]

end Algebraic.Cutwidth.Extractor.Internal
