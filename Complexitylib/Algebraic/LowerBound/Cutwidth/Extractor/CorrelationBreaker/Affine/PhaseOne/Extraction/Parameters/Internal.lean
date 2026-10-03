/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Bounds
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final

/-!
# Closing the finite parameters of the actual first affine phase

The explicit chooser supplies every numerical guard and pays the two
original-source mass contributions. Only original probability, source-cap,
uniform-right-input, and advice hypotheses remain in the actual pairwise
output theorems. The selected source threshold need not fit every input.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

theorem affinePhaseOne_left_pair_parameters_dist_le (n t a target : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t (affinePhaseOneRightBits n t a target))
    (advice : Option (Fin t) → List Bool) (i : Fin t) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) =
      uniformWeight (Fin (affinePhaseOneRightBits n t a target) → Bool))
    (honest_length : (advice none).length = a)
    (tampered_length : (advice (some i)).length = a) (different : advice none ≠ advice (some i))
    (source : (∑ z, μ z) ≤ ((2 : ℝ) ^ (affinePhaseOneSourceEntropy n t a target))⁻¹) :
    let d := affinePhaseOneRightBits n t a target
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a target
    let L₁ := affinePhaseOneScale n t a target
    let e := affinePhaseOneLocalError target
    let actual := affinePhaseOneLeftPairWeight n d t h L₀ e L₁ (adviceErrorExponent a e) e
      w l r x mask ys advice i
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ := by
  subst a
  have growing := affinePhaseOneParameters_growing_guard n t (advice none).length target
  have bound := affinePhaseOne_left_pair_dist_le n
    (affinePhaseOneRightBits n t (advice none).length target) t (growingMatchedBlockDepth t)
    (affinePhaseOneInitialScale n t (advice none).length target) (affinePhaseOneLocalError target)
    (affinePhaseOneScale n t (advice none).length target) (affinePhaseOneLocalError target)
    (affinePhaseOneLocalError target) w l r x mask ys advice i μ
    (affinePhaseOneParameters_initial_length n t _ target)
    (affinePhaseOneParameters_initial_room n t _ target)
    (affinePhaseOneParameters_initial_error n t _ target)
    (affinePhaseOneParameters_prefix_size n t _ target)
    (affinePhaseOneParameters_advice_guard n t _ target)
    (affinePhaseOneParameters_output_size n t _ target)
    growing.1 growing.2.1 growing.2.2 hw hl hr nonnegative cap uniform
    tampered_length.symm different
    (affinePhaseOneParameters_source_budget n t _ target)
    (affinePhaseOneParameters_seed_width n t _ target)
  exact bound.trans (affinePhaseOneError_dyadic_le _ _ _ _ target _
    (affinePhaseOneParameters_initial_reserve n t _ target)
    (affinePhaseOneParameters_final_reserve n t _ target) source)

theorem affinePhaseOne_pair_parameters_dist_le (n t a target : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t (affinePhaseOneRightBits n t a target))
    (advice : Option (Fin t) → List Bool) (i : Fin t) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) =
      uniformWeight (Fin (affinePhaseOneRightBits n t a target) → Bool))
    (honest_length : (advice none).length = a)
    (tampered_length : (advice (some i)).length = a) (different : advice none ≠ advice (some i))
    (source : (∑ z, μ z) ≤ ((2 : ℝ) ^ (affinePhaseOneSourceEntropy n t a target))⁻¹) :
    let d := affinePhaseOneRightBits n t a target
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a target
    let L₁ := affinePhaseOneScale n t a target
    let e := affinePhaseOneLocalError target
    let actual := affinePhaseOnePairWeight n d t h L₀ e L₁ (adviceErrorExponent a e) e
      w l r x mask ys advice i
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ := by
  exact (affinePhaseOnePair_dist_le_left n (affinePhaseOneRightBits n t a target) t
    (growingMatchedBlockDepth t) (affinePhaseOneInitialScale n t a target)
    (affinePhaseOneLocalError target) (affinePhaseOneScale n t a target)
    (adviceErrorExponent a (affinePhaseOneLocalError target)) (affinePhaseOneLocalError target)
    w l r x mask ys advice i).trans
      (affinePhaseOne_left_pair_parameters_dist_le n t a target w l r x mask ys advice i μ
        hw hl hr nonnegative cap uniform honest_length tampered_length different source)

end Algebraic.Cutwidth.Extractor.Internal
