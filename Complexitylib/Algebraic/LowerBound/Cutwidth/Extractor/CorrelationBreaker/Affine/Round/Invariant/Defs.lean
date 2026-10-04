/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs

/-!
# Near-uniformity against every sufficiently small tampering set

The honest old left row is compared with uniform while retaining the actual
transcript and any set of at most `k` tampered left rows. The capacity is an
upper bound, so empty subsets and non-powers-of-two are included naturally.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Every subset within the capacity obeys the same actual retained-row bound. -/
def AffineRowInvariant (h t L : Nat) {Z A : Type*} [Fintype Z] [Fintype A]
    (w : Z → ℝ) (l : Z → A → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L)) (k : Nat) (ρ : ℝ) : Prop :=
  ∀ S : Finset (Fin t), S.card ≤ k →
    weightDist (affineRoundLeftRowsWeight h t L w l wl S)
      (uniformSecondWeight (affineRoundLeftRowsWeight h t L w l wl S)) ≤ ρ

end Algebraic.Cutwidth.Extractor
