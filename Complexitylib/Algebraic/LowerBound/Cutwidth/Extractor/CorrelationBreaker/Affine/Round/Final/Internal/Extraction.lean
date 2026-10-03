/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional

/-!
# Consuming the actual final-seed discrepancy

Apply two-sided leakage to the selected tuple of tampered next-left rows.
The full right state then reconstructs all final seed observations. The
only entropy charge beyond the supplied middle-transcript envelope is the
selected output tuple's exact alphabet size.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineRoundLeftSubset_dist_le_of_middleEnvelope (n d h t L e K : Nat)
    {ε δ : ℝ} (extract : WeightedStrongSeededExtractor (matchedBlockExtractor n h L e) K ε)
    (error : 0 ≤ ε) {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (μ : AffineRoundMiddleTranscript Z t L → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, affineRoundMiddleWeight d h t L e w l r wl wr ys z *
      mapWeight (x z.1.1.1.1) (affineRoundMiddleLeft h t L e l wl z) x₀ ≤ μ z)
    (seed : weightDist (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)
      (uniformSecondWeight (affineRoundFinalSeedWeight d h t L e w l r wl wr ys S)) ≤ δ) :
    weightDist (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
      (uniformSecondWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) ≤
        ε + δ + (K : ℝ) * (Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) : ℝ) ^
          S.card * ∑ z, μ z := by
  obtain ⟨hw₁, hl₁, hr₁⟩ := affineRoundMiddle_probability d h t L e w l r wl wr ys hw hl hr
  have jointCap (z : AffineRoundMiddleTranscript Z t L) (u : Unit) (x₀ : Fin n → Bool) :
      affineRoundMiddleWeight d h t L e w l r wl wr ys z *
        mapWeight (fun a => (((), x z.1.1.1.1 a) : Unit × (Fin n → Bool)))
          (affineRoundMiddleLeft h t L e l wl z) (u, x₀) ≤ μ z := by
    cases u
    have joint : mapWeight (fun a => (((), x z.1.1.1.1 a) : Unit × (Fin n → Bool)))
        (affineRoundMiddleLeft h t L e l wl z) ((), x₀) =
        mapWeight (x z.1.1.1.1) (affineRoundMiddleLeft h t L e l wl z) x₀ := by
      unfold mapWeight
      apply Finset.sum_congr rfl
      intro a _
      by_cases same : x z.1.1.1.1 a = x₀ <;> simp [same]
    rw [joint]
    exact cap z x₀
  have bound := extract.two_sided_leakage_dist_le error
    (affineRoundMiddleWeight d h t L e w l r wl wr ys)
    (affineRoundMiddleLeft h t L e l wl)
    (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
    (fun z => x z.1.1.1.1)
    (fun z b => affineRoundFinalSeedRight d t L e ys z b none)
    (fun _ _ => ())
    (fun z b (i : S) => affineRoundFinalSeedRight d t L e ys z b (some i.val))
    (fun z seeds a (i : S) => matchedBlockExtractor n h L e (x z.1.1.1.1 a) (seeds i))
    (fun zu : AffineRoundMiddleTranscript Z t L × Unit => μ zu.1)
    hw₁ hl₁ hr₁ (fun zu => nonnegative zu.1) jointCap seed
  have projected := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight (affineRoundMiddleWeight d h t L e w l r wl wr ys)
      (affineRoundMiddleLeft h t L e l wl)
      (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
      (fun z => x z.1.1.1.1)
      (fun z b => affineRoundFinalSeedRight d t L e ys z b none)
      (fun _ _ => ())
      (fun z b (i : S) => affineRoundFinalSeedRight d t L e ys z b (some i.val))
      (fun z seeds a (i : S) => matchedBlockExtractor n h L e (x z.1.1.1.1 a) (seeds i))
      (matchedBlockExtractor n h L e)) (affineRoundFinalSubsetTag d h t L e ys S)
  rw [affineRoundLeftSubsetWeight_eq_project n d h t L e w l r x wl wr ys S hl hr] at projected
  apply projected.trans
  have card : (Fintype.card (S → Fin (matchedBlockOutputBits h L) → Bool) : ℝ) =
      (Fintype.card (Fin (matchedBlockOutputBits h L) → Bool) : ℝ) ^ S.card := by
    rw [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow]
  rw [card] at bound
  simpa only [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton] using bound

end Algebraic.Cutwidth.Extractor.Internal
