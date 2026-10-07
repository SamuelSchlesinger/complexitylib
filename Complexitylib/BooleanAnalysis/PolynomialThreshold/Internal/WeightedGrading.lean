/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.ProjectionBlocks
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.ProjectionTrace
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.WalshDimensions
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.CoordinateMultipliers

/-!
# Gotsman--Linial: WeightedGrading

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/WeightedGrading.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# The actual weighted orthogonal grading of the cube

The construction first orthogonalizes an arbitrary finite flag of subspaces.
It then transports the concrete Walsh flag by the invertible square-root
weight and takes the orthogonal projections in the counting Hilbert space.
The resulting matrices are proved to form an orthogonal decomposition of
the identity with the prescribed binomial multiplicities.
-/

noncomputable section

open scoped BigOperators
open Module

namespace BooleanAnalysis.PolynomialThreshold.Internal

section FiniteFlag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- The new orthogonal layer appearing between two consecutive stages of a flag. -/
def flagLayer (K : ℕ → Submodule 𝕜 E) (k : ℕ) : Submodule 𝕜 E :=
  K (k + 1) ⊓ (K k)ᗮ

/-- The actual orthogonal projection onto a layer of a finite-dimensional flag. -/
def flagProjection (K : ℕ → Submodule 𝕜 E) (k : ℕ) : E →L[𝕜] E :=
  (flagLayer K k).starProjection

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_le_next (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagLayer K k ≤ K (k + 1) := inf_le_left

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_le_prev_orthogonal (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagLayer K k ≤ (K k)ᗮ := inf_le_right

theorem flagLayer_sup_prev (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    K k ⊔ flagLayer K k = K (k + 1) := by
  simpa only [flagLayer, inf_comm] using
    Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hK (Nat.le_succ k))

theorem flagLayer_finrank_add (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    finrank 𝕜 (K k) + finrank 𝕜 (flagLayer K k) = finrank 𝕜 (K (k + 1)) := by
  change finrank 𝕜 (K k) + finrank 𝕜 (K (k + 1) ⊓ (K k)ᗮ : Submodule 𝕜 E) = _
  rw [inf_comm]
  exact Submodule.finrank_add_inf_finrank_orthogonal (hK (Nat.le_succ k))

theorem flagLayer_finrank (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    finrank 𝕜 (flagLayer K k) = finrank 𝕜 (K (k + 1)) - finrank 𝕜 (K k) := by
  have h := flagLayer_finrank_add K hK k
  omega

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_isOrtho_of_lt (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r < s) : flagLayer K r ⟂ flagLayer K s := by
  apply Submodule.IsOrtho.symm
  exact (flagLayer_le_prev_orthogonal K s).trans
    (Submodule.orthogonal_le ((flagLayer_le_next K r).trans (hK hrs)))

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_isOrtho (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r ≠ s) : flagLayer K r ⟂ flagLayer K s := by
  rcases lt_or_gt_of_ne hrs with h | h
  · exact flagLayer_isOrtho_of_lt K hK h
  · exact (flagLayer_isOrtho_of_lt K hK h).symm

theorem flagLayer_iSup_eq_top (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (hzero : K 0 = ⊥) (n : ℕ) (htop : K (n + 1) = ⊤) :
    (⨆ k : Fin (n + 1), flagLayer K k.val) = ⊤ := by
  let S := ⨆ k : Fin (n + 1), flagLayer K k.val
  have hle : ∀ m, m ≤ n + 1 → K m ≤ S := by
    intro m
    induction m with
    | zero => simp [hzero]
    | succ m ih =>
      intro hm
      rw [← flagLayer_sup_prev K hK m]
      exact sup_le (ih (by omega))
        (le_iSup (fun k : Fin (n + 1) => flagLayer K k.val) ⟨m, by omega⟩)
  apply top_unique
  rw [← htop]
  exact hle (n + 1) le_rfl

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_orthogonalFamily (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (n : ℕ) :
    OrthogonalFamily 𝕜 (fun k : Fin (n + 1) => flagLayer K k.val)
      (fun k => (flagLayer K k.val).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro r s hrs
  exact flagLayer_isOrtho K hK (fun h => hrs (Fin.ext h))

theorem flagProjection_isSelfAdjoint (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    IsSelfAdjoint (flagProjection K k) :=
  isSelfAdjoint_starProjection (flagLayer K k)

theorem flagProjection_idempotent (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagProjection K k * flagProjection K k = flagProjection K k :=
  (flagLayer K k).isIdempotentElem_starProjection.eq

theorem flagProjection_mul_eq_zero (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r ≠ s) : flagProjection K r * flagProjection K s = 0 :=
  (flagLayer_isOrtho K hK hrs).starProjection_comp_starProjection

theorem sum_flagProjection (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (hzero : K 0 = ⊥) (n : ℕ) (htop : K (n + 1) = ⊤) :
    (∑ k : Fin (n + 1), flagProjection K k.val) = 1 := by
  ext x
  change (∑ k : Fin (n + 1), (flagLayer K k.val).starProjection) x = x
  rw [sum_apply]
  apply (flagLayer_orthogonalFamily K hK n).sum_projection_of_mem_iSup
  rw [flagLayer_iSup_eq_top K hK hzero n htop]
  trivial

@[simp]
theorem range_flagProjection (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    (flagProjection K k).range = flagLayer K k :=
  Submodule.range_starProjection (flagLayer K k)

theorem flagProjection_apply_mem_next (K : ℕ → Submodule 𝕜 E) (k : ℕ) (x : E) :
    flagProjection K k x ∈ K (k + 1) :=
  (flagLayer K k).starProjection_apply_mem x |>.1

theorem flagProjection_apply_eq_zero_of_mem_prev (K : ℕ → Submodule 𝕜 E)
    (k : ℕ) {x : E} (hx : x ∈ K k) : flagProjection K k x = 0 := by
  have ho : x ∈ (flagLayer K k)ᗮ :=
    Submodule.orthogonal_le (flagLayer_le_prev_orthogonal K k)
      ((K k).le_orthogonal_orthogonal hx)
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr ho)

end FiniteFlag

section InvertibleWeights

variable {Ω : Type*} [Fintype Ω]

/-- Multiplication by pointwise nonzero coefficients is a linear equivalence. -/
def coordinateMulEquiv (a : Ω → ℂ) (ha : ∀ x, a x ≠ 0) :
    (Ω → ℂ) ≃ₗ[ℂ] (Ω → ℂ) where
  toFun f x := a x * f x
  invFun f x := (a x)⁻¹ * f x
  left_inv f := by
    funext x
    simp only [← mul_assoc, inv_mul_cancel₀ (ha x), one_mul]
  right_inv f := by
    funext x
    simp only [← mul_assoc, mul_inv_cancel₀ (ha x), one_mul]
  map_add' f g := by
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    funext x
    exact mul_left_comm _ _ _

/-- Multiplication by the square root of a strictly positive weight, in the
counting Euclidean Hilbert space. -/
def sqrtWeightEquiv (w : Ω → ℝ) (hw : ∀ x, 0 < w x) :
    EuclideanSpace ℂ Ω ≃ₗ[ℂ] EuclideanSpace ℂ Ω :=
  ((WithLp.linearEquiv 2 ℂ (Ω → ℂ)).trans
    (coordinateMulEquiv (fun x => (Real.sqrt (w x) : ℂ))
      (fun x => Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (hw x)))))).trans
    (WithLp.linearEquiv 2 ℂ (Ω → ℂ)).symm

omit [Fintype Ω] in
@[simp]
theorem sqrtWeightEquiv_apply (w : Ω → ℝ) (hw : ∀ x, 0 < w x)
    (f : EuclideanSpace ℂ Ω) (x : Ω) :
    sqrtWeightEquiv w hw f x = (Real.sqrt (w x) : ℂ) * f x := rfl

omit [Fintype Ω] in
@[simp]
theorem sqrtWeightEquiv_symm_apply (w : Ω → ℝ) (hw : ∀ x, 0 < w x)
    (f : EuclideanSpace ℂ Ω) (x : Ω) :
    (sqrtWeightEquiv w hw).symm f x = (Real.sqrt (w x) : ℂ)⁻¹ * f x := rfl

end InvertibleWeights

section Transport

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- Transport a degree flag through an invertible linear weight operator. -/
def transportFlag (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E) (k : ℕ) :
    Submodule 𝕜 E := (F k).map D.toLinearMap

theorem transportFlag_monotone (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (hF : Monotone F) : Monotone (transportFlag D F) := by
  intro i j hij
  exact Submodule.map_mono (hF hij)

theorem transportFlag_zero (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (hF : F 0 = ⊥) : transportFlag D F 0 = ⊥ := by
  simp [transportFlag, hF]

theorem transportFlag_top (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (k : ℕ) (hF : F k = ⊤) : transportFlag D F k = ⊤ := by
  simp [transportFlag, hF]

theorem transportFlag_finrank (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E) (k : ℕ) :
    finrank 𝕜 (transportFlag D F k) = finrank 𝕜 (F k) :=
  D.finrank_map_eq (F k)

/-- The weighted construction preserves every prescribed dimension increment. -/
theorem transportFlag_layer_finrank [FiniteDimensional 𝕜 E] (D : E ≃ₗ[𝕜] E)
    (F : ℕ → Submodule 𝕜 E) (hF : Monotone F) (k d : ℕ)
    (hd : finrank 𝕜 (F k) + d = finrank 𝕜 (F (k + 1))) :
    finrank 𝕜 (flagLayer (transportFlag D F) k) = d := by
  have h := flagLayer_finrank_add (transportFlag D F) (transportFlag_monotone D F hF) k
  rw [transportFlag_finrank, transportFlag_finrank] at h
  omega

end Transport

section MatrixTransport

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Matrix of an actual flag-layer projection in an orthonormal basis. -/
def flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) : Matrix ι ι ℂ :=
  operatorMatrix b (flagProjection K k)

/-- The matrix projection-family laws follow from the constructed Hilbert-space
projections, without any additional grading hypothesis. -/
theorem flagProjectionMatrix_family (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (hK : Monotone K) (hzero : K 0 = ⊥)
    (n : ℕ) (htop : K (n + 1) = ⊤) :
    OrthogonalProjectionFamily (fun k : Fin (n + 1) => flagProjectionMatrix b K k.val) :=
  orthogonalProjectionFamily_operatorMatrix b
    (fun k : Fin (n + 1) => flagProjection K k.val)
    (fun k => flagProjection_isSelfAdjoint K k.val)
    (fun k => flagProjection_idempotent K k.val)
    (fun _ _ hrs => flagProjection_mul_eq_zero K hK (fun h => hrs (Fin.ext h)))
    (sum_flagProjection K hK hzero n htop)

theorem trace_flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) :
    Matrix.trace (flagProjectionMatrix b K k) = (finrank ℂ (flagLayer K k) : ℂ) :=
  trace_toMatrixOrthonormal_starProjection b (flagLayer K k)

theorem re_trace_flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) :
    (Matrix.trace (flagProjectionMatrix b K k)).re = (finrank ℂ (flagLayer K k) : ℝ) :=
  re_trace_toMatrixOrthonormal_starProjection b (flagLayer K k)

end MatrixTransport

section WeightedCube

variable {n : ℕ}

/-- The weighted degree-`k` subspace of the counting Hilbert space. -/
def weightedFourierSpace (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  (fourierEuclideanSpace n k).map (sqrtWeightEquiv w hw).toLinearMap

/-- The weighted Fourier flag, shifted by one so that stage zero is bottom. -/
def weightedFourierFlag (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    ℕ → Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)

@[simp]
theorem weightedFourierFlag_zero (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    weightedFourierFlag w hw 0 = ⊥ :=
  transportFlag_zero _ _ (fourierFlag_zero n)

@[simp]
theorem weightedFourierFlag_succ (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : ℕ) :
    weightedFourierFlag w hw (k + 1) = weightedFourierSpace w hw k := rfl

theorem weightedFourierFlag_mono (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    Monotone (weightedFourierFlag w hw) :=
  transportFlag_monotone _ _ (fourierFlag_mono n)

theorem weightedFourierFlag_top (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    weightedFourierFlag w hw (n + 1) = ⊤ :=
  transportFlag_top _ _ _ (fourierFlag_top n)

/-- Weighting preserves the exact binomial dimensions of the orthogonal layers. -/
theorem weightedFourierFlag_layer_finrank (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : ℕ) :
    finrank ℂ (flagLayer (weightedFourierFlag w hw) k) = n.choose k :=
  transportFlag_layer_finrank (sqrtWeightEquiv w hw) (fourierFlag n)
    (fourierFlag_mono n) k (n.choose k) (fourierFlag_finrank_add n k)

/-- Actual orthogonal projection onto weighted Fourier layer `k`. -/
def weightedProjection (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : Fin (n + 1)) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  flagProjection (weightedFourierFlag w hw) k.val

/-- The projection represented in the point-mass orthonormal basis. -/
def weightedProjectionMatrix (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) : Matrix (Cube n) (Cube n) ℂ :=
  flagProjectionMatrix (EuclideanSpace.basisFun (Cube n) ℂ)
    (weightedFourierFlag w hw) k.val

theorem weightedProjection_apply_mem (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) (f : EuclideanSpace ℂ (Cube n)) :
    weightedProjection w hw k f ∈ weightedFourierSpace w hw k.val :=
  flagProjection_apply_mem_next (weightedFourierFlag w hw) k.val f

theorem weightedProjection_annihilate_prev (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) {f : EuclideanSpace ℂ (Cube n)}
    (hf : f ∈ weightedFourierFlag w hw k.val) : weightedProjection w hw k f = 0 :=
  flagProjection_apply_eq_zero_of_mem_prev (weightedFourierFlag w hw) k.val hf

theorem weightedProjectionMatrix_family (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    OrthogonalProjectionFamily (weightedProjectionMatrix w hw) :=
  flagProjectionMatrix_family (EuclideanSpace.basisFun (Cube n) ℂ)
    (weightedFourierFlag w hw) (weightedFourierFlag_mono w hw)
    (weightedFourierFlag_zero w hw) n (weightedFourierFlag_top w hw)

theorem weightedProjectionMatrix_trace (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) :
    Matrix.trace (weightedProjectionMatrix w hw k) = (n.choose k.val : ℂ) := by
  rw [weightedProjectionMatrix, trace_flagProjectionMatrix, weightedFourierFlag_layer_finrank]

theorem weightedProjectionMatrix_trace_re (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) :
    (Matrix.trace (weightedProjectionMatrix w hw k)).re = (n.choose k.val : ℝ) := by
  rw [weightedProjectionMatrix_trace]
  simp

theorem weightedProjectionMatrix_hsNormSq (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) : hsNormSq (weightedProjectionMatrix w hw k) = (n.choose k.val : ℝ) := by
  rw [hsNormSq_projection _ ((weightedProjectionMatrix_family w hw).conjTranspose_eq k)
    ((weightedProjectionMatrix_family w hw).idempotent k)]
  exact weightedProjectionMatrix_trace_re w hw k

/-- Every real diagonal multiplier commutes with the positive square-root weight. -/
theorem sqrtWeightEquiv_commute_signMultiplier
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (h : Cube n → ℝ)
    (f : EuclideanSpace ℂ (Cube n)) :
    signMultiplier h (sqrtWeightEquiv w hw f) =
      sqrtWeightEquiv w hw (signMultiplier h f) := by
  ext x
  simp only [signMultiplier_apply, sqrtWeightEquiv_apply]
  exact mul_left_comm _ _ _

theorem sqrtWeightEquiv_commute_coordinateMultiplier
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n)
    (f : EuclideanSpace ℂ (Cube n)) :
    coordinateMultiplier i (sqrtWeightEquiv w hw f) =
      sqrtWeightEquiv w hw (coordinateMultiplier i f) :=
  sqrtWeightEquiv_commute_signMultiplier w hw (fun x => cubeCoord x i) f

end WeightedCube

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity
