/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Statement
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.PolynomialDegree
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.CoordinateMultipliers
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.SignParity
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.WeightedGrading
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.ProjectionBlocks
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Ring

/-!
# Gotsman--Linial: BlockVanishing

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/BlockVanishing.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Vanishing of low antidiagonal blocks

The geometric step is reduced to an explicit finite sum: multiplication on
both sides by the square root of a positive weight turns the weighted pairing
into a Fourier pairing against the signed weight.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace BooleanAnalysis.PolynomialThreshold.Internal

/-- The threshold convention at zero is compatible with the signed absolute
value identity used to build the weighted grading. -/
theorem abs_mul_thresholdSign (t : ℝ) : |t| * thresholdSign t = t := by
  by_cases ht : 0 ≤ t
  · simp [thresholdSign, ht, abs_of_nonneg ht]
  · simp [thresholdSign, ht, abs_of_neg (lt_of_not_ge ht)]

/-- If the image of one subspace under an operator is orthogonal to a second
subspace, the corresponding projection block vanishes. -/
theorem projectionBlock_eq_zero_of_pairing
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (H : E →L[𝕜] E)
    (hpair : ∀ u ∈ U, ∀ v ∈ V, inner 𝕜 v (H u) = 0) :
    V.starProjection * H * U.starProjection = 0 := by
  ext x
  change V.starProjection (H (U.starProjection x)) = 0
  apply (Submodule.starProjection_apply_eq_zero_iff V).mpr
  intro v hv
  exact hpair _ (U.starProjection_apply_mem x) v hv

/-- Lift an orthogonality calculation on preimages through a common linear map
to a zero block between subspaces of its images. -/
theorem projectionBlock_eq_zero_of_map_pairing
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (A B U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : E →ₗ[𝕜] E) (H : E →L[𝕜] E)
    (hU : U ≤ A.map D) (hV : V ≤ B.map D)
    (hpair : ∀ a ∈ A, ∀ b ∈ B, inner 𝕜 (D b) (H (D a)) = 0) :
    V.starProjection * H * U.starProjection = 0 := by
  apply projectionBlock_eq_zero_of_pairing U V H
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := hU hu
  obtain ⟨b, hb, rfl⟩ := hV hv
  exact hpair a ha b hb

/-- The finite pairing identity underlying the low antidiagonal cutoff.
The norm and inner product are the counting Euclidean ones. -/
theorem sqrtWeight_inner_eq_sum
    {Ω : Type*} [Fintype Ω]
    (w h : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D : EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω)
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω)
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ Ω) :
    inner ℂ (D b) (H (D a)) =
      ∑ x, star (b x) * a x * ((w x : ℂ) * (h x : ℂ)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [RCLike.inner_apply', hH, hD, hD]
  calc
    star ((Real.sqrt (w x) : ℂ) * b x) *
        ((h x : ℂ) * ((Real.sqrt (w x) : ℂ) * a x)) =
      star (b x) * a x *
        (((Real.sqrt (w x) : ℂ) * (Real.sqrt (w x) : ℂ)) * (h x : ℂ)) := by
          simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
          ring
    _ = star (b x) * a x * ((w x : ℂ) * (h x : ℂ)) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw x)]

/-- Replace the weight times the diagonal sign by the actual signed weight. -/
theorem sqrtWeight_inner_eq_sum_signedWeight
    {Ω : Type*} [Fintype Ω]
    (w h : Ω → ℝ) (q : Ω → ℂ) (hw : ∀ x, 0 ≤ w x)
    (hwq : ∀ x, (w x : ℂ) * (h x : ℂ) = q x)
    (D : EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω)
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω)
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ Ω) :
    inner ℂ (D b) (H (D a)) = ∑ x, star (b x) * a x * q x := by
  rw [sqrtWeight_inner_eq_sum w h hw D hD H hH]
  simp only [hwq]

/-- High Fourier support of the signed weight kills every pairing whose two
unweighted degrees have smaller total degree. -/
theorem sqrtWeight_pairing_eq_zero_of_fourier_separation
    {n r s k : ℕ} (w h : Cube n → ℝ) (q : Cube n → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hwq : ∀ x, (w x : ℂ) * (h x : ℂ) = q x)
    (D : EuclideanSpace ℂ (Cube n) →ₗ[ℂ] EuclideanSpace ℂ (Cube n))
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n))
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ (Cube n))
    (ha : WithLp.ofLp a ∈ fourierSpace n r)
    (hb : WithLp.ofLp b ∈ fourierSpace n s)
    (hq : q ∈ fourierSpaceFrom n k) (hrs : r + s < k) :
    inner ℂ (D b) (H (D a)) = 0 := by
  rw [sqrtWeight_inner_eq_sum_signedWeight w h q hw hwq D hD H hH]
  exact sum_mul_eq_zero_of_fourier_separated (fourierSpace_conj_mul ha hb) hq hrs

/-- The choices `w = |p|` and `h = parity * sign(p)` multiply to the
high-degree signed polynomial, including at a zero of the polynomial. -/
theorem polynomial_signedWeight {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Cube n) :
    ((|polynomialValue p x| : ℝ) : ℂ) *
        ((fullParity x * thresholdSign (polynomialValue p x) : ℝ) : ℂ) =
      walshChar Finset.univ x * (polynomialValue p x : ℂ) := by
  rw [Complex.ofReal_mul]
  calc
    ((|polynomialValue p x| : ℝ) : ℂ) *
        ((fullParity x : ℂ) * (thresholdSign (polynomialValue p x) : ℂ)) =
      (fullParity x : ℂ) *
        (((|polynomialValue p x| : ℝ) : ℂ) *
          (thresholdSign (polynomialValue p x) : ℂ)) := by ring
    _ = walshChar Finset.univ x * (polynomialValue p x : ℂ) := by
      rw [← Complex.ofReal_mul, abs_mul_thresholdSign]
      simp only [fullParity, walshChar, Complex.ofReal_prod]

/-- The weighted pairing vanishes for the polynomial, weight,
and parity-modified threshold sign.  No Fourier-support assumption remains. -/
theorem polynomial_sqrtWeight_pairing_eq_zero
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (a b : EuclideanSpace ℂ (Cube n))
    (ha : WithLp.ofLp a ∈ fourierSpace n r)
    (hb : WithLp.ofLp b ∈ fourierSpace n s) (hrs : r + s < n - d) :
    let D := sqrtWeightEquiv (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    inner ℂ (D b)
      (signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) (D a))
        = 0 := by
  dsimp only
  apply sqrtWeight_pairing_eq_zero_of_fourier_separation
    (fun x => |polynomialValue p x|)
    (fun x => fullParity x * thresholdSign (polynomialValue p x))
    (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ))
    (fun x => abs_nonneg (polynomialValue p x)) (polynomial_signedWeight p)
    _ (fun a x => sqrtWeightEquiv_apply _ _ a x)
    _ (fun a x => signMultiplier_apply _ a x) a b ha hb
    (parity_polynomialValue_mem_fourierSpaceFrom hp hd) hrs

/-- The operator between two subspaces of weighted low-degree spaces is zero
below the polynomial's degree cutoff. -/
theorem polynomial_projectionBlock_eq_zero
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (U V : Submodule ℂ (EuclideanSpace ℂ (Cube n)))
    (hU : U ≤ weightedFourierSpace (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x)) r)
    (hV : V ≤ weightedFourierSpace (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x)) s)
    (hrs : r + s < n - d) :
    V.starProjection *
      signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) *
        U.starProjection = 0 := by
  apply projectionBlock_eq_zero_of_map_pairing
    (fourierEuclideanSpace n r) (fourierEuclideanSpace n s) U V
    (sqrtWeightEquiv (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))).toLinearMap _ hU hV
  intro a ha b hb
  apply polynomial_sqrtWeight_pairing_eq_zero (r := r) (s := s) p hp hd hnz a b
  · simpa only [mem_fourierEuclideanSpace] using ha
  · simpa only [mem_fourierEuclideanSpace] using hb
  · exact hrs

/-- Low antidiagonal vanishing for the actual weighted grading constructed
from the polynomial.  All geometric hypotheses are discharged. -/
theorem weightedFlag_block_eq_zero_of_polynomial_degree
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0) (hrs : r + s < n - d) :
    let K := weightedFourierFlag (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    flagProjection K s *
      signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) *
        flagProjection K r = 0 := by
  dsimp only
  apply polynomial_projectionBlock_eq_zero (r := r) (s := s) p hp hd hnz
  · simpa only [weightedFourierFlag_succ] using
      flagLayer_le_next
        (weightedFourierFlag (fun x => |polynomialValue p x|)
          (fun x => abs_pos.mpr (hnz x))) r
  · simpa only [weightedFourierFlag_succ] using
      flagLayer_le_next
        (weightedFourierFlag (fun x => |polynomialValue p x|)
          (fun x => abs_pos.mpr (hnz x))) s
  · exact hrs

/-- The same vanishing statement in any orthonormal matrix coordinates, ready
for the Hilbert-Schmidt block coupling. -/
theorem weightedFlag_matrixBlock_eq_zero_of_polynomial_degree
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0) (hrs : r + s < n - d)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Cube n))) :
    let K := weightedFourierFlag (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    operatorMatrix b (flagProjection K s) *
      operatorMatrix b
        (signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x))) *
      operatorMatrix b (flagProjection K r) = 0 := by
  have h := congrArg (operatorMatrix b)
    (weightedFlag_block_eq_zero_of_polynomial_degree p hp hd hnz hrs)
  simpa only [operatorMatrix_mul, operatorMatrix_zero] using h

/-- The concrete cutoff used by the finite block coupling: actual weighted
projection matrices, actual diagonal parity-modified polynomial threshold,
and no unproved construction assumptions. -/
theorem weightedProjectionMatrix_block_eq_zero_of_polynomial_degree
    {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (r s : Fin (n + 1)) (hrs : r.val + s.val < n - d) :
    let w := fun x => |polynomialValue p x|
    let hw : ∀ x, 0 < w x := fun x => abs_pos.mpr (hnz x)
    weightedProjectionMatrix w hw s *
      signMatrix (fun x => fullParity x * polynomialThreshold p x) *
        weightedProjectionMatrix w hw r = 0 := by
  have h := weightedFlag_matrixBlock_eq_zero_of_polynomial_degree
    (r := r.val) (s := s.val) p hp hd hnz hrs (EuclideanSpace.basisFun (Cube n) ℂ)
  simpa only [weightedProjectionMatrix, flagProjectionMatrix, signMultiplier,
    operatorMatrix_toEuclideanCLM, polynomialThreshold] using h

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity
