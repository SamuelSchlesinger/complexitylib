/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript

/-!
# Exact original-law projection for the final round call

The original right state reconstructs the complete final-seed vector from
the middle transcript. Therefore retaining all final seed observations
after extraction is a deterministic operation on already retained data.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem observedSeedWeight_eq_factored {Z A B V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (y : Z → B → Seed) (hl : ∀ z, IsProbabilityWeight (l z)) :
    observedSeedWeight w r v y =
      mapWeight (fun p : (Z × B) × A =>
        ((p.1.1, v p.1.1 p.1.2), y p.1.1 p.1.2)) (factoredWeight w l r) := by
  have marginal : mapWeight Prod.fst (factoredWeight w l r) =
      fun zb => w zb.1 * r zb.1 zb.2 := by
    rw [mapWeight_fst]
    funext zb
    simp only [firstWeight, factoredWeight, ← Finset.mul_sum, (hl _).2, mul_one]
  unfold observedSeedWeight
  rw [← marginal, mapWeight_comp]

theorem affineRoundFinalSeedWeight_eq_map (d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    affineRoundFinalSeedWeight d h t L e w l r wl wr ys S =
      mapWeight (fun p : (Z × B) × A =>
        let seeds := fun i => affineRoundFinalSeed d h L e (ys p.1.1 p.1.2 i)
          (fun j => Bool.xor (wl p.1.1 p.2 i j) (wr p.1.1 p.1.2 i j))
        ((affineRoundMiddleTranscript d h t L e wl wr ys p,
          fun i : S => seeds (some i.val)), seeds none)) (factoredWeight w l r) := by
  have hp : ∀ z, IsProbabilityWeight (affineRoundPrefixLeft h t L l wl z) :=
    observedTranscriptKernel_probability _ _ (fun z => hl z.1)
  have hl₁ : ∀ z, IsProbabilityWeight (affineRoundMiddleLeft h t L e l wl z) :=
    observedTranscriptKernel_probability _ _ (fun z => hp z.1)
  unfold affineRoundFinalSeedWeight
  rw [observedSeedWeight_eq_factored _ (affineRoundMiddleLeft h t L e l wl) _ _ _ hl₁,
    ← affineRoundMiddle_factored d h t L e w l r wl wr ys hl hr, mapWeight_comp]
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  simp only [affineRoundFinalSeedRight_eq]

/-- Reconstruct all final right messages while preserving the selected output tuple. -/
def affineRoundFinalSubsetTag (d h t L e : Nat) {Z B : Type*}
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (p : (AffineRoundMiddleTranscript Z t L × B) ×
      (Unit × (S → Fin (matchedBlockOutputBits h L) → Bool))) :
    (AffineRoundTranscript Z t L × B) × (S → Fin (matchedBlockOutputBits h L) → Bool) :=
  (((p.1.1, affineRoundFinalSeedRight d t L e ys p.1.1 p.1.2), p.1.2), p.2.2)

theorem affineRoundLeftSubsetWeight_eq_project (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p => (affineRoundFinalSubsetTag d h t L e ys S p.1, p.2))
      (twoSidedExtractionWeight (affineRoundMiddleWeight d h t L e w l r wl wr ys)
        (affineRoundMiddleLeft h t L e l wl)
        (fun z => affineRoundMiddleRightKernel d h t L e r wr ys z.1)
        (fun z => x z.1.1.1.1)
        (fun z b => affineRoundFinalSeedRight d t L e ys z b none)
        (fun _ _ => ())
        (fun z b (i : S) => affineRoundFinalSeedRight d t L e ys z b (some i.val))
        (fun z seeds a (i : S) => matchedBlockExtractor n h L e (x z.1.1.1.1 a) (seeds i))
        (matchedBlockExtractor n h L e)) =
      affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S := by
  rw [twoSidedExtractionWeight_eq_map,
    ← affineRoundMiddle_factored d h t L e w l r wl wr ys hl hr,
    mapWeight_comp, mapWeight_comp]
  unfold affineRoundLeftSubsetWeight
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply, affineRoundFinalSubsetTag]
  rw [affineRoundFinalSeedRight_eq]
  dsimp only [affineRoundOutputLeft, affineRoundTranscript, affineRoundMiddleTranscript,
    affineRoundMiddleRightTranscript, affineRoundPrefixTranscript, affineRoundPrefixMaskTranscript]

theorem affineRoundLeftSubsetWeight_probability (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem affineRoundSubsetWeight_probability (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S) :=
  (factoredWeight_probability w l r hw hl hr).map _

end Algebraic.Cutwidth.Extractor.Internal
