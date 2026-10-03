/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Recovering the actual masked output pair

The retained transcript and original right state determine both final
output masks. XORing the honest output is a fiberwise bijection; applying
the tampered mask is deterministic processing of the retained tag. Thus
the actual masked pair costs no additional conditional-uniformity error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def outputXorEquiv {ι : Type*} (mask : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x i := Bool.xor (x i) (mask i)
  invFun x i := Bool.xor (x i) (mask i)
  left_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl
  right_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl

private def honestMaskEquiv (n t h L₀ L₁ er : Nat) {Z B : Type*}
    (mask : Z → B → Fin n → Bool)
    (p : (AffinePhaseOneTranscript Z t L₀ L₁ × B) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool)) :
    (Fin (matchedBlockOutputBits h L₁) → Bool) ≃ (Fin (matchedBlockOutputBits h L₁) → Bool) :=
  outputXorEquiv (affinePhaseOneOutputRight n t h L₀ L₁ er mask p.1.1 p.1.2 none)

private def maskedPairTag (n t h L₀ L₁ er : Nat) {Z B : Type*}
    (mask : Z → B → Fin n → Bool) (i : Fin t)
    (p : (AffinePhaseOneTranscript Z t L₀ L₁ × B) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool)) :
    (AffinePhaseOneTranscript Z t L₀ L₁ × B) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool) :=
  (p.1, fun j => Bool.xor (p.2 j)
    (affinePhaseOneOutputRight n t h L₀ L₁ er mask p.1.1 p.1.2 (some i) j))

private theorem pairWeight_eq_mask (n d t h L₀ e₀ L₁ e₁ er : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) :
    affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i =
      mapWeight (fun p => (maskedPairTag n t h L₀ L₁ er mask i p.1, p.2))
        (mapWeight (fun p => (p.1, honestMaskEquiv n t h L₀ L₁ er mask p.1 p.2))
          (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) := by
  unfold affinePhaseOnePairWeight affinePhaseOneLeftPairWeight
  rw [mapWeight_comp, mapWeight_comp]
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [maskedPairTag, honestMaskEquiv, outputXorEquiv, Equiv.coe_fn_mk]
  rw [affinePhaseOneOutput_eq_xor n d t h L₀ e₀ L₁ e₁ er x mask ys advice p (some i),
    affinePhaseOneOutput_eq_xor n d t h L₀ e₀ L₁ e₁ er x mask ys advice p none]

theorem affinePhaseOnePair_dist_le_left (n d t h L₀ e₀ L₁ e₁ er : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) :
    weightDist
      (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
      (uniformSecondWeight
        (affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) ≤
      weightDist
        (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
        (uniformSecondWeight
          (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)) := by
  have projected := weightDist_uniformSecond_map_first_le
    (mapWeight (fun p => (p.1, honestMaskEquiv n t h L₀ L₁ er mask p.1 p.2))
      (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i))
    (maskedPairTag n t h L₀ L₁ er mask i)
  rw [← pairWeight_eq_mask n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i,
    weightDist_uniformSecond_fiberEquiv] at projected
  exact projected

end Algebraic.Cutwidth.Extractor.Internal
