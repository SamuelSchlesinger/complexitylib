/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Internal.Projection
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Parameters

/-!
# First-phase subset initialization from original sources

A positive number of tamperings supplies an index even for the empty
subset. Every subset of cardinality at most one is contained in a
singleton; its actual law is a marginal of the checked pair law.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

theorem affinePhaseOne_left_subset_dist_le (n d t h L₀ e₀ L₁ target er : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (μ : Z → ℝ) (positive : 0 < t) (small : S.card ≤ 1)
    (length : Nat.clog 2 (n + 1) ≤ L₀) (room : 64 ≤ L₀) (error : e₀ + 64 + 2 ≤ L₀)
    (size : matchedBlockSeedBits L₀ ≤ d)
    (guard : FlipFlopSizeGuard d (matchedBlockOutputBits 64 L₀) L₁
      (adviceErrorExponent (advice none).length target))
    (output_size : matchedBlockOutputBits 64 L₁ ≤ matchedBlockOutputBits 64 L₀)
    (final_length : Nat.clog 2 (n + 1) ≤ L₁)
    (final_error : er + h + 2 ≤ L₁)
    (final_budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) = uniformWeight (Fin d → Bool))
    (advice_length : ∀ i, (advice none).length = (advice (some i)).length)
    (different : ∀ i, advice none ≠ advice (some i))
    (source_budget : 2 ^ 150 * ((advice none).length + 1) * L₁ +
      (t + 1) * (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀) ≤ d)
    (seed_width : 2 ^ 150 * ((advice none).length + 1) * L₁ ≤ matchedBlockOutputBits 64 L₀) :
    let e₁ := adviceErrorExponent (advice none).length target
    let actual := affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er
      w l r x mask ys advice S
    weightDist actual (uniformSecondWeight actual) ≤
      affinePhaseOneError t h L₀ e₀ L₁ target er (∑ z, μ z) := by
  let : Nonempty (Fin t) := ⟨⟨0, positive⟩⟩
  obtain ⟨i, selected⟩ := Finset.card_le_one_iff_subset_singleton.mp small
  exact (affinePhaseOneLeftRowsWeight_dist_le_pair n d t h L₀ e₀ L₁ _ er
    w l r x mask ys advice S i selected (fun z => (hl z).1) hr).trans
    (affinePhaseOne_left_pair_dist_le n d t h L₀ e₀ L₁ target er
      w l r x mask ys advice i μ length room error size guard output_size
      final_length final_error final_budget hw hl hr nonnegative cap uniform
      (advice_length i) (different i) source_budget seed_width)

theorem affinePhaseOne_left_subset_parameters_dist_le (n t a target : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t (affinePhaseOneRightBits n t a target))
    (advice : Option (Fin t) → List Bool) (S : Finset (Fin t)) (μ : Z → ℝ)
    (positive : 0 < t) (small : S.card ≤ 1)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) =
      uniformWeight (Fin (affinePhaseOneRightBits n t a target) → Bool))
    (honest_length : (advice none).length = a)
    (tampered_length : ∀ i, (advice (some i)).length = a)
    (different : ∀ i, advice none ≠ advice (some i))
    (source : (∑ z, μ z) ≤ ((2 : ℝ) ^ (affinePhaseOneSourceEntropy n t a target))⁻¹) :
    let d := affinePhaseOneRightBits n t a target
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a target
    let L₁ := affinePhaseOneScale n t a target
    let e := affinePhaseOneLocalError target
    let actual := affinePhaseOneLeftRowsWeight n d t h L₀ e L₁ (adviceErrorExponent a e) e
      w l r x mask ys advice S
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ := by
  let : Nonempty (Fin t) := ⟨⟨0, positive⟩⟩
  obtain ⟨i, selected⟩ := Finset.card_le_one_iff_subset_singleton.mp small
  exact (affinePhaseOneLeftRowsWeight_dist_le_pair n _ t _ _ _ _ _ _
    w l r x mask ys advice S i selected (fun z => (hl z).1) hr).trans
    (affinePhaseOne_left_pair_parameters_dist_le n t a target
      w l r x mask ys advice i μ hw hl hr nonnegative cap uniform
      honest_length (tampered_length i) (different i) source)

end Algebraic.Cutwidth.Extractor.Internal
