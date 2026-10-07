/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.CoordinateMultipliers
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.HilbertSchmidt
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Tactic

/-!
# Gotsman--Linial: CubeOperators

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/CubeOperators.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Coordinate commutators and Hamming-distance energy

The coordinate sign matrices are the actual diagonal operators of the Boolean
cube. The identities here turn their Hilbert--Schmidt and entry estimates into
the energy estimates used by the edge-recovery argument.
-/

open scoped BigOperators

namespace BooleanAnalysis.PolynomialThreshold.Internal

variable {n : ℕ}

/-- In the point basis, a coordinate commutator records the difference of the
two endpoint signs. -/
theorem coordinate_commutator_apply
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    (M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y =
      (((cubeCoord y i - cubeCoord x i : ℝ) : ℂ)) * M x y := by
  simp only [coordinateSignMatrix, signMatrix, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.ofReal_sub]
  ring

/-- Squaring a coordinate difference gives four exactly on the coordinates
where the Boolean endpoints differ. -/
theorem coordinate_commutator_sq_norm
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 =
      (if x i ≠ y i then (4 : ℝ) else 0) * ‖M x y‖ ^ 2 := by
  rw [coordinate_commutator_apply, norm_mul, mul_pow]
  congr 1
  cases hx : x i <;> cases hy : y i <;> norm_num [cubeCoord, hx, hy]

/-- Summing the squared entries over coordinates counts Hamming distance. -/
theorem sum_coordinate_commutator_sq_norm
    (M : Matrix (Cube n) (Cube n) ℂ) (x y : Cube n) :
    (∑ i : Fin n,
      ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2) =
      4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
  classical
  simp_rw [coordinate_commutator_sq_norm, ite_mul, zero_mul]
  calc
    (∑ i : Fin n, if x i ≠ y i then 4 * ‖M x y‖ ^ 2 else 0) =
        ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), 4 * ‖M x y‖ ^ 2 := by
      rw [Finset.sum_filter]
    _ = (hammingDist x y : ℝ) * (4 * ‖M x y‖ ^ 2) := by
      simp [hammingDist, nsmul_eq_mul]
    _ = 4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by ring

/-- The total coordinate-commutator energy is four times the distance-weighted
entry energy. -/
theorem sum_hsNormSq_coordinate_commutator
    (M : Matrix (Cube n) (Cube n) ℂ) :
    (∑ i : Fin n, hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M)) =
      4 * ∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
  classical
  simp only [hsNormSq]
  calc
    (∑ i : Fin n, ∑ x : Cube n, ∑ y : Cube n,
        ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2) =
        ∑ x : Cube n, ∑ y : Cube n, ∑ i : Fin n,
          ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x : Cube n, ∑ y : Cube n,
        4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
      simp_rw [sum_coordinate_commutator_sq_norm]
    _ = 4 * ∑ x : Cube n, ∑ y : Cube n,
        (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
      simp only [Finset.mul_sum, mul_assoc]

/-- A uniform coordinate-commutator Hilbert--Schmidt bound gives the distance
energy inequality for the actual cube matrix. -/
theorem distance_energy_le_of_coordinate_commutator_bound
    (M : Matrix (Cube n) (Cube n) ℂ)
    (hbound : ∀ i : Fin n,
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n) :
    (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hbound i)
  rw [sum_hsNormSq_coordinate_commutator] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- A coordinate at which distinct endpoints differ turns an entrywise
commutator estimate into the edge-entry cap `1/4`. -/
theorem off_diagonal_sq_norm_le_quarter_of_commutator_bound
    (M : Matrix (Cube n) (Cube n) ℂ)
    (hbound : ∀ (i : Fin n) (x y : Cube n),
      ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 ≤ 1)
    (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    exact not_not.mp (not_exists.mp h i)
  have h := hbound i x y
  rw [coordinate_commutator_sq_norm, ite_eq_left hi] at h
  linarith

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
