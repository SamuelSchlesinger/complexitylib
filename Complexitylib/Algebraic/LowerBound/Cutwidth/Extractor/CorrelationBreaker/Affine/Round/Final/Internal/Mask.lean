/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Final.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Recovering actual masked next rows

The complete transcript and original right state determine every output
mask. The honest XOR is a fiberwise bijection and the selected tampered
XORs are deterministic processing of the retained tag. This conversion
adds no conditional-uniformity error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def outputXorEquiv {ι : Type*} (mask : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x i := Bool.xor (x i) (mask i)
  invFun x i := Bool.xor (x i) (mask i)
  left_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl
  right_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl

private def honestMaskEquiv (n h t L e : Nat) {Z B : Type*}
    (mask : Z → B → Fin n → Bool) (S : Finset (Fin t))
    (p : (AffineRoundTranscript Z t L × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) :
    (Fin (matchedBlockOutputBits h L) → Bool) ≃ (Fin (matchedBlockOutputBits h L) → Bool) :=
  outputXorEquiv (affineRoundOutputRight n h t L e mask p.1.1 p.1.2 none)

private def maskedSubsetTag (n h t L e : Nat) {Z B : Type*}
    (mask : Z → B → Fin n → Bool) (S : Finset (Fin t))
    (p : (AffineRoundTranscript Z t L × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) :
    (AffineRoundTranscript Z t L × B) × (S → Fin (matchedBlockOutputBits h L) → Bool) :=
  (p.1, fun i j => Bool.xor (p.2 i j)
    (affineRoundOutputRight n h t L e mask p.1.1 p.1.2 (some i.val) j))

private theorem subsetWeight_eq_mask (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) :
    affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S =
      mapWeight (fun p => (maskedSubsetTag n h t L e mask S p.1, p.2))
        (mapWeight (fun p => (p.1, honestMaskEquiv n h t L e mask S p.1 p.2))
          (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) := by
  unfold affineRoundSubsetWeight affineRoundLeftSubsetWeight
  rw [mapWeight_comp, mapWeight_comp]
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply, maskedSubsetTag, honestMaskEquiv, outputXorEquiv,
    Equiv.coe_fn_mk]
  simp only [affineRoundOutput_eq_xor]

theorem affineRoundSubset_dist_le_left (n d h t L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (wl : Z → A → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (wr : Z → B → AffinePhaseOneCopies t (matchedBlockOutputBits h L))
    (ys : Z → B → AffinePhaseOneCopies t d) (S : Finset (Fin t)) :
    weightDist (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)
      (uniformSecondWeight (affineRoundSubsetWeight n d h t L e w l r x mask wl wr ys S)) ≤
      weightDist (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)
        (uniformSecondWeight (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S)) := by
  have projected := weightDist_uniformSecond_map_first_le
    (mapWeight (fun p => (p.1, honestMaskEquiv n h t L e mask S p.1 p.2))
      (affineRoundLeftSubsetWeight n d h t L e w l r x wl wr ys S))
    (maskedSubsetTag n h t L e mask S)
  rw [← subsetWeight_eq_mask n d h t L e w l r x mask wl wr ys S,
    weightDist_uniformSecond_fiberEquiv] at projected
  exact projected

end Algebraic.Cutwidth.Extractor.Internal
