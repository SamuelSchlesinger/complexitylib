/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Distance
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript

/-!
# Actual masked rows with the full right state retained

Conditional independence allows the unchanged right state to be appended
to a left-row law without changing its distance from conditional uniform.
All right output masks are then known from the retained state. Honest XOR
is a fiberwise bijection and masking the selected rows processes only the
retained tag, so neither operation adds error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {n d h t L : Nat} {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

theorem affineIterationState_leftSubsetWeight_dist_eq
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t))
    (hw : ∀ z, 0 ≤ s.weight z) (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    weightDist (s.leftSubsetWeight S) (uniformSecondWeight (s.leftSubsetWeight S)) =
      weightDist (affineRoundLeftRowsWeight h t L s.weight s.left s.leftRows S)
        (uniformSecondWeight (affineRoundLeftRowsWeight h t L s.weight s.left s.leftRows S)) := by
  have bound := observedSeedWeight_observe_other_dist s.weight s.left s.right
    (fun _ b => b) (fun z a => fun j : S => s.leftRows z a (some j.val))
    (fun z a => s.leftRows z a none) hw hr
  have identity (z : Z) : mapWeight (fun b : B => b) (s.right z) = s.right z :=
    mapWeight_id _
  have factors : (fun p : (Z × B) × A => s.weight p.1.1 * s.right p.1.1 p.1.2 *
      s.left p.1.1 p.2) = factoredWeight s.weight s.left s.right := rfl
  simpa only [AffineIterationState.leftSubsetWeight, affineRoundLeftRowsWeight,
    observedSeedWeight, observedTranscriptWeight, identity, factors] using bound

private def rowXorEquiv {ι : Type*} (mask : ι → Bool) : (ι → Bool) ≃ (ι → Bool) where
  toFun x i := Bool.xor (x i) (mask i)
  invFun x i := Bool.xor (x i) (mask i)
  left_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl
  right_inv x := by funext i; dsimp only; cases x i <;> cases mask i <;> rfl

private def honestMaskEquiv (s : AffineIterationState n d h t L Z A B)
    (S : Finset (Fin t))
    (p : (Z × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) :
    (Fin (matchedBlockOutputBits h L) → Bool) ≃ (Fin (matchedBlockOutputBits h L) → Bool) :=
  rowXorEquiv (s.rightRows p.1.1 p.1.2 none)

private def maskedSubsetTag (s : AffineIterationState n d h t L Z A B)
    (S : Finset (Fin t))
    (p : (Z × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) :
    (Z × B) × (S → Fin (matchedBlockOutputBits h L) → Bool) :=
  (p.1, fun j k => Bool.xor (p.2 j k) (s.rightRows p.1.1 p.1.2 (some j.val) k))

private theorem subsetWeight_eq_mask
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t)) :
    s.subsetWeight S =
      mapWeight (fun p => (maskedSubsetTag s S p.1, p.2))
        (mapWeight (fun p => (p.1, honestMaskEquiv s S p.1 p.2)) (s.leftSubsetWeight S)) := by
  simp only [AffineIterationState.subsetWeight, AffineIterationState.leftSubsetWeight,
    mapWeight_comp, maskedSubsetTag, honestMaskEquiv, rowXorEquiv, Equiv.coe_fn_mk]

theorem affineIterationState_subsetWeight_dist_le_left
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t)) :
    weightDist (s.subsetWeight S) (uniformSecondWeight (s.subsetWeight S)) ≤
      weightDist (s.leftSubsetWeight S) (uniformSecondWeight (s.leftSubsetWeight S)) := by
  have projected := weightDist_uniformSecond_map_first_le
    (mapWeight (fun p => (p.1, honestMaskEquiv s S p.1 p.2)) (s.leftSubsetWeight S))
    (maskedSubsetTag s S)
  rw [← subsetWeight_eq_mask s S, weightDist_uniformSecond_fiberEquiv] at projected
  exact projected

theorem affineIterationState_subsetWeight_probability
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t))
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    IsProbabilityWeight (s.subsetWeight S) :=
  (factoredWeight_probability s.weight s.left s.right hw hl hr).map _

theorem affineIterationState_subsetWeight_dist_le
    (s : AffineIterationState n d h t L Z A B) (S : Finset (Fin t))
    {k : Nat} {ρ : ℝ} (hw : ∀ z, 0 ≤ s.weight z)
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (invariant : AffineRowInvariant h t L s.weight s.left s.leftRows k ρ)
    (size : S.card ≤ k) :
    weightDist (s.subsetWeight S) (uniformSecondWeight (s.subsetWeight S)) ≤ ρ := by
  have bound := affineIterationState_subsetWeight_dist_le_left s S
  rw [affineIterationState_leftSubsetWeight_dist_eq s S hw hr] at bound
  exact bound.trans (invariant S size)

end Algebraic.Cutwidth.Extractor.Internal
