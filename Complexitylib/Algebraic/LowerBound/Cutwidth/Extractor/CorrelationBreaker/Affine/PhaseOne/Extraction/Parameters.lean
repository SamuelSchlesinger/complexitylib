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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Parameters.Internal

/-!
# The chosen first affine phase from original sources

The explicit finite chooser discharges all numerical guards in the actual
pairwise extraction theorem. A normalized original source with the chosen
entropy reserve and a uniform honest right input yields error at most
`2^-target` against each distinct equal-length advice string. Both laws
retain the complete executed transcript and original right state.

The first-phase pattern is from Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Theorem 6.1,
<https://arxiv.org/pdf/2110.12652>. The parameters here are deliberately
conservative. This establishes the pairwise initial guarantee; the
subset-doubling rounds of `Affine.Round` and `Affine.Iteration` upgrade it to
joint affine security (`affineCorrelationBreaker_parameters_dist_le`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- The chosen parameters give the actual left-contribution bound from original sources. -/
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
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affinePhaseOne_left_pair_parameters_dist_le n t a target
    w l r x mask ys advice i μ hw hl hr nonnegative cap uniform
    honest_length tampered_length different source

/-- The chosen parameters give the actual masked-output bound from original sources. -/
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
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affinePhaseOne_pair_parameters_dist_le n t a target
    w l r x mask ys advice i μ hw hl hr nonnegative cap uniform
    honest_length tampered_length different source

end Algebraic.Cutwidth.Extractor
