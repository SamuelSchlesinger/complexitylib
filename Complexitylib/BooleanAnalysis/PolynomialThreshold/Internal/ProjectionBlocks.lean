/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.HilbertSchmidt
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic

/-!
# Gotsman--Linial: ProjectionBlocks

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/ProjectionBlocks.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Matrix blocks of a finite orthogonal projection family

The Hilbert--Schmidt quantity below is the explicit sum of squared entry norms
rather than an ambient matrix norm instance.
-/

open scoped BigOperators ComplexConjugate
open Module

noncomputable section

namespace BooleanAnalysis.PolynomialThreshold.Internal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A finite orthogonal decomposition of the identity by Hermitian projections. -/
structure OrthogonalProjectionFamily (P : κ → Matrix ι ι ℂ) : Prop where
  selfAdjoint : ∀ k, IsSelfAdjoint (P k)
  idempotent : ∀ k, P k * P k = P k
  orthogonal : ∀ r s, r ≠ s → P r * P s = 0
  sum_eq_one : ∑ k, P k = 1

namespace OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)

include hP

theorem conjTranspose_eq (k : κ) : (P k).conjTranspose = P k := by
  simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using hP.selfAdjoint k

theorem mul_eq_ite [DecidableEq κ] (r s : κ) :
    P r * P s = if r = s then P r else 0 := by
  by_cases hrs : r = s
  · subst s
    simp [hP.idempotent]
  · simp [hrs, hP.orthogonal r s hrs]

end OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ}

theorem sum_projection_blocks (hP : OrthogonalProjectionFamily P) (B : Matrix ι ι ℂ) :
    (∑ r, ∑ s, P s * B * P r) = B := by
  simp_rw [← Matrix.sum_mul, hP.sum_eq_one, Matrix.one_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one]

theorem projection_block_ext (hP : OrthogonalProjectionFamily P)
    {A B : Matrix ι ι ℂ} (h : ∀ r s, P s * A * P r = P s * B * P r) : A = B := by
  rw [← sum_projection_blocks hP A, ← sum_projection_blocks hP B]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => h r s

/-- The real-valued spectral multiplier defined by the projection family. -/
def matrixGrading (P : κ → Matrix ι ι ℂ) (weight : κ → ℝ) : Matrix ι ι ℂ :=
  ∑ k, (weight k : ℂ) • P k

theorem projection_mul_matrixGrading (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (s : κ) : P s * matrixGrading P weight = (weight s : ℂ) • P s := by
  classical
  simp only [matrixGrading, Matrix.mul_sum, Matrix.mul_smul, hP.mul_eq_ite]
  simp

theorem matrixGrading_mul_projection (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (r : κ) : matrixGrading P weight * P r = (weight r : ℂ) • P r := by
  classical
  simp only [matrixGrading, Matrix.sum_mul, Matrix.smul_mul, hP.mul_eq_ite]
  simp

theorem projection_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B - B * matrixGrading P weight) * P r =
      ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  calc
    P s * (matrixGrading P weight * B) * P r -
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r -
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r -
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_sub, sub_smul]

theorem projection_anticommutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B + B * matrixGrading P weight) * P r =
      ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_add, Matrix.add_mul]
  calc
    P s * (matrixGrading P weight * B) * P r +
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r +
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r +
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_add, add_smul]

omit [DecidableEq ι] in
theorem trace_projection_sandwich (Q A : Matrix ι ι ℂ) (hQ : Q * Q = Q) :
    Matrix.trace (Q * A * Q) = Matrix.trace (Q * A) := by
  rw [Matrix.trace_mul_cycle, hQ]

theorem hsNormSq_projection_mul (hP : OrthogonalProjectionFamily P)
    (s : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (P s * B) = (Matrix.trace (B.conjTranspose * P s * B)).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  congr 2
  calc
    (B.conjTranspose * P s) * (P s * B) =
        B.conjTranspose * (P s * P s) * B := by simp only [Matrix.mul_assoc]
    _ = B.conjTranspose * P s * B := by rw [hP.idempotent]

theorem hsNormSq_mul_projection (hP : OrthogonalProjectionFamily P)
    (r : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (B * P r) = (Matrix.trace (P r * (B.conjTranspose * B))).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  have heq : (P r * B.conjTranspose) * (B * P r) =
      P r * (B.conjTranspose * B) * P r := by simp only [Matrix.mul_assoc]
  rw [heq, trace_projection_sandwich _ _ (hP.idempotent r)]

theorem hsNormSq_left_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ s, hsNormSq (P s * B) := by
  simp_rw [hsNormSq_projection_mul hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum]
  simp_rw [← Matrix.sum_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one, hsNormSq_eq_re_trace]

theorem hsNormSq_right_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ r, hsNormSq (B * P r) := by
  simp_rw [hsNormSq_mul_projection hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    hP.sum_eq_one, Matrix.one_mul, hsNormSq_eq_re_trace]

theorem hsNormSq_block_parseval (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq B = ∑ r, ∑ s, hsNormSq (P s * B * P r) := by
  rw [hsNormSq_right_projection_decomposition hP B]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Matrix.mul_assoc] using hsNormSq_left_projection_decomposition hP (B * P r)

theorem hsNormSq_matrixGrading (hP : OrthogonalProjectionFamily P) (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * hsNormSq (P r) := by
  classical
  rw [hsNormSq_block_parseval hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [projection_mul_matrixGrading hP, Matrix.smul_mul, hP.idempotent,
      hsNormSq_real_smul]
  · intro s _ hsr
    rw [projection_mul_matrixGrading hP, Matrix.smul_mul,
      hP.orthogonal s r hsr, smul_zero, hsNormSq_zero]
  · simp

theorem hsNormSq_matrixGrading_trace (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * (Matrix.trace (P r)).re := by
  rw [hsNormSq_matrixGrading hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [hsNormSq_projection (P r) (hP.conjTranspose_eq r) (hP.idempotent r)]

theorem sum_hsNormSq_blocks_column (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r : κ) (hB : B.conjTranspose * B = 1) :
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (P r) := by
  calc
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (B * P r) := by
      simpa only [Matrix.mul_assoc] using
        (hsNormSq_left_projection_decomposition hP (B * P r)).symm
    _ = hsNormSq (P r) := hsNormSq_mul_left_of_unitary B (P r) hB

theorem sum_hsNormSq_blocks_row (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (s : κ) (hB : B * B.conjTranspose = 1) :
    (∑ r, hsNormSq (P s * B * P r)) = hsNormSq (P s) := by
  rw [← hsNormSq_right_projection_decomposition hP (P s * B)]
  exact hsNormSq_mul_right_of_unitary (P s) B hB

theorem sum_hsNormSq_blocks_column_trace (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r : κ) (hB : B.conjTranspose * B = 1) :
    (∑ s, hsNormSq (P s * B * P r)) = (Matrix.trace (P r)).re := by
  rw [sum_hsNormSq_blocks_column hP B r hB]
  exact hsNormSq_projection (P r) (hP.conjTranspose_eq r) (hP.idempotent r)

theorem sum_hsNormSq_blocks_row_trace (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (s : κ) (hB : B * B.conjTranspose = 1) :
    (∑ r, hsNormSq (P s * B * P r)) = (Matrix.trace (P s)).re := by
  rw [sum_hsNormSq_blocks_row hP B s hB]
  exact hsNormSq_projection (P s) (hP.conjTranspose_eq s) (hP.idempotent s)

theorem hsNormSq_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) :
    hsNormSq (matrixGrading P weight * B - B * matrixGrading P weight) =
      ∑ r, ∑ s, (weight s - weight r) ^ 2 * hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_commutator hP, hsNormSq_real_smul]

theorem hsNormSq_anticommutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) :
    hsNormSq (matrixGrading P weight * B + B * matrixGrading P weight) =
      ∑ r, ∑ s, (weight s + weight r) ^ 2 * hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_anticommutator hP, hsNormSq_real_smul]

/-- The degree grading associated to projections indexed from zero to `n`. -/
def degreeGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ)

/-- The degree grading centered at `n / 2`. -/
def centeredGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ) - (n : ℝ) / 2

theorem hsNormSq_centeredGrading {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    hsNormSq (centeredGrading P) =
      ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * hsNormSq (P k) :=
  hsNormSq_matrixGrading hP _

theorem hsNormSq_centeredGrading_trace {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    hsNormSq (centeredGrading P) =
      ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * (Matrix.trace (P k)).re :=
  hsNormSq_matrixGrading_trace hP _

theorem centeredGrading_eq {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    centeredGrading P = degreeGrading P - (((n : ℝ) / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  simp only [centeredGrading, degreeGrading, matrixGrading, Complex.ofReal_sub, sub_smul,
    Finset.sum_sub_distrib]
  rw [← Finset.smul_sum, hP.sum_eq_one]

theorem projection_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r s : Fin (n + 1)) :
    P s * (centeredGrading P * B + B * centeredGrading P) * P r =
      (((s.val : ℝ) + (r.val : ℝ) - n : ℝ) : ℂ) • (P s * B * P r) := by
  rw [centeredGrading, projection_anticommutator hP]
  congr 2
  ring

theorem hsNormSq_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq (centeredGrading P * B + B * centeredGrading P) =
      ∑ r, ∑ s, ((s.val : ℝ) + (r.val : ℝ) - n) ^ 2 *
        hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_centered_anticommutator hP, hsNormSq_real_smul]

section OperatorTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Matrix representation of a continuous operator in an orthonormal basis,
bundled with its algebraic compatibility. -/
def operatorMatrixEquiv (b : OrthonormalBasis ι ℂ E) :
    (E →L[ℂ] E) ≃ₐ[ℂ] Matrix ι ι ℂ :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).symm.trans
    (LinearMap.toMatrixOrthonormal b).toAlgEquiv

/-- Matrix entries for the counting orthonormal basis or any chosen
orthonormal basis. -/
def operatorMatrix (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) : Matrix ι ι ℂ :=
  operatorMatrixEquiv b T

theorem operatorMatrix_eq_toMatrix (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) :
    operatorMatrix b T = LinearMap.toMatrixOrthonormal b T.toLinearMap := rfl

theorem operatorMatrix_apply (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (i j : ι) :
    operatorMatrix b T i j = inner ℂ (b i) (T (b j)) :=
  LinearMap.toMatrixOrthonormal_apply_apply b T.toLinearMap i j

theorem operatorMatrix_injective (b : OrthonormalBasis ι ℂ E) :
    Function.Injective (operatorMatrix b) := (operatorMatrixEquiv b).injective

@[simp]
theorem operatorMatrix_zero (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (0 : E →L[ℂ] E) = 0 := map_zero (operatorMatrixEquiv b)

@[simp]
theorem operatorMatrix_one (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (1 : E →L[ℂ] E) = 1 := map_one (operatorMatrixEquiv b)

@[simp]
theorem operatorMatrix_add (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A + B) = operatorMatrix b A + operatorMatrix b B :=
  map_add (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_sub (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A - B) = operatorMatrix b A - operatorMatrix b B :=
  map_sub (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_mul (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A * B) = operatorMatrix b A * operatorMatrix b B :=
  map_mul (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_smul (b : OrthonormalBasis ι ℂ E) (z : ℂ) (T : E →L[ℂ] E) :
    operatorMatrix b (z • T) = z • operatorMatrix b T :=
  (operatorMatrixEquiv b).toLinearEquiv.map_smul z T

@[simp]
theorem operatorMatrix_sum (b : OrthonormalBasis ι ℂ E) (T : κ → E →L[ℂ] E) :
    operatorMatrix b (∑ k, T k) = ∑ k, operatorMatrix b (T k) :=
  map_sum (operatorMatrixEquiv b) T Finset.univ

theorem operatorMatrix_isSelfAdjoint (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) : IsSelfAdjoint (operatorMatrix b T) := by
  have hlin : IsSelfAdjoint T.toLinearMap :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff T).mpr hT
  exact hlin.map (LinearMap.toMatrixOrthonormal b)

/-- Transfer an actually constructed orthogonal family of Hilbert-space
projections to the matrix interface used by the block estimates. -/
theorem orthogonalProjectionFamily_operatorMatrix (b : OrthonormalBasis ι ℂ E)
    (T : κ → E →L[ℂ] E)
    (hself : ∀ k, IsSelfAdjoint (T k))
    (hidem : ∀ k, T k * T k = T k)
    (horth : ∀ r s, r ≠ s → T r * T s = 0)
    (hsum : ∑ k, T k = 1) :
    OrthogonalProjectionFamily (fun k => operatorMatrix b (T k)) where
  selfAdjoint k := operatorMatrix_isSelfAdjoint b (T k) (hself k)
  idempotent k := by rw [← operatorMatrix_mul, hidem k]
  orthogonal r s hrs := by rw [← operatorMatrix_mul, horth r s hrs, operatorMatrix_zero]
  sum_eq_one := by rw [← operatorMatrix_sum, hsum, operatorMatrix_one]

end OperatorTransport

/-- The standard-basis matrix representation is inverse to the standard
Euclidean continuous linear operator associated to a matrix. -/
@[simp]
theorem operatorMatrix_toEuclideanCLM (A : Matrix ι ι ℂ) :
    operatorMatrix (EuclideanSpace.basisFun ι ℂ)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) = A :=
  (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun ι ℂ)).apply_symm_apply A

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity
