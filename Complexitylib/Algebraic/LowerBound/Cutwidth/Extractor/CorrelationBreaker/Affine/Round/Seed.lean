/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Internal

/-!
# Actual masked prefixes and first right seeds of an affine round

A balanced prefix of the old honest row remains nearly uniform while
retaining the selected tampered rows. Observing independent right masks
and applying their known XOR values preserves this bound. The following
actual right extraction pays its selected output alphabet and the one
right prefix-mask observation against the original right-source envelope.

This supplies the first alternating step of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The old retained-subset law is normalized. -/
theorem affineRoundLeftRowsWeight_probability (h t L : Nat)
    {Z A : Type*} [Fintype Z] [Fintype A] (w : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z)) :
    IsProbabilityWeight (affineRoundLeftRowsWeight h t L w l wl S) :=
  Internal.affineRoundLeftRowsWeight_probability
    h t L w l wl S hw hl

/-- The actual masked-prefix seed law is normalized. -/
theorem affineRoundPrefixSeedWeight_probability (h t L : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundPrefixSeedWeight h t L w l r wl wr S) :=
  Internal.affineRoundPrefixSeedWeight_probability
    h t L w l r wl wr S hw hl hr

/-- The first executed right-seed law is normalized. -/
theorem affineRoundMiddleSeedWeight_probability (d h t L e : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundMiddleSeedWeight d h t L e w l r wl wr ys S) :=
  Internal.affineRoundMiddleSeedWeight_probability
    d h t L e w l r wl wr ys S hw hl hr

/-- A long enough prefix maps the uniform row exactly to uniform. -/
theorem affineRoundPrefix_uniform (h L : Nat)
    (size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L) :
    mapWeight (affineRoundPrefix h L)
      (uniformWeight (Fin (matchedBlockOutputBits h L) → Bool)) =
        uniformWeight (Fin (matchedBlockSeedBits L) → Bool) :=
  Internal.affineRoundPrefix_uniform
    h L size

/-- Actual masked prefixes inherit the old retained-subset discrepancy. -/
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
          (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl S)) :=
  Internal.affineRoundPrefixSeed_dist_le
    h t L size w l r wl wr S hw hr

/-- The first actual right extraction follows from the old row and original source envelope. -/
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
          Fintype.card (AffineRoundShortMessages t L) * ∑ z, ν z :=
  Internal.affineRoundMiddleSeed_dist_le
    d h t L e size length room error w l r wl wr ys S ν hw hl hr nonnegative cap old

end Algebraic.Cutwidth.Extractor
