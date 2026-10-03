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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Recovery.Internal

/-!
# Actual final seeds from the original right source

The actual short-row guarantee seeds a second extraction on the original
right word. Its envelope accounts for every prior right observation, while
the retained law records all actual short rows and the selected tampered
final seeds. This is the recovery call in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual short-row guarantee and original right envelope control the executed final seed. -/
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
          (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ 3 * ∑ z, ν z :=
  Internal.affineRoundFinalSeed_dist_le
    d h t L e length room error w l r wl wr ys S ν hw hl hr nonnegative cap seed

end Algebraic.Cutwidth.Extractor
