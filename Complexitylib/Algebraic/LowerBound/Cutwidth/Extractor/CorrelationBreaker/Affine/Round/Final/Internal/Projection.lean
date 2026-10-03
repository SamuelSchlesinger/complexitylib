/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# The final left rows form the next round's actual subset law

Discarding the retained original right state gives exactly the next
left-row law at the full transcript. Conditional-uniformity discrepancy
therefore contracts without an additional repair or averaging error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundNextLeftRows_eq_map (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    affineRoundLeftRowsWeight h t L (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
      (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x) S =
      mapWeight (fun p => ((p.1.1.1, p.1.2), p.2))
        (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S) := by
  have full := affineRoundTranscript_probability d h t L e w l r wl wr ys hw hl hr
  unfold affineRoundLeftRowsWeight observedSeedWeight
  rw [← factoredWeight_right_marginal _ (affineRoundTranscriptRight d h t L e r wr ys)
    _ full.2.2, ← factoredWeight_swap, mapWeight_comp,
    ← affineRoundTranscript_factored d h t L e w l r wl wr ys hl hr, mapWeight_comp]
  unfold affineRoundLeftSubsetWeight
  simp only [mapWeight_comp]

theorem affineRoundNextLeftRows_dist_le (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist
      (affineRoundLeftRowsWeight h t L (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
        (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x) S)
      (uniformSecondWeight
        (affineRoundLeftRowsWeight h t L (affineRoundTranscriptWeight d h t L e w l r wl wr ys)
          (affineRoundTranscriptLeft h t L e l wl) (affineRoundOutputLeft n h t L e x) S)) ≤
      weightDist (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
        (uniformSecondWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) := by
  have projected := weightDist_uniformSecond_map_first_le
    (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
    (fun p => (p.1.1, p.2))
  rw [← affineRoundNextLeftRows_eq_map n d h t L e w l r x wl wr ys S hw hl hr] at projected
  exact projected

end Algebraic.Cutwidth.Extractor.Internal
