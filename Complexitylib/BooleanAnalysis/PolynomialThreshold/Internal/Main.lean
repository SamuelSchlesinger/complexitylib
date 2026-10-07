/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Statement
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.BlockCoupling
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Commutator
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.CubeOperators
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.EdgeRecovery
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.GradingShift
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.BlockVanishing
public import Mathlib.Tactic.Ring

/-!
# Gotsman--Linial: Main

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/Main.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Assembly of the Gotsman--Linial average-sensitivity bound

The first lemmas are explicitly conditional assembly bridges. The final
theorems discharge their matrix and counting hypotheses using the concrete
weighted Boolean-cube grading and a sign-preserving constant perturbation.
-/

namespace BooleanAnalysis.PolynomialThreshold.Internal

open scoped BigOperators

/-- The two analytic constants combine to the constant `8` after
normalizing by the number of cube vertices. This is only a scalar bridge. -/
theorem normalized_edge_bound {N C T a : ℝ} (hN : 0 < N)
    (hedge : C ≤ 2 * T) (henergy : T ≤ 4 * a * N) :
    C / N ≤ 8 * a := by
  apply (div_le_iff₀ hN).mpr
  calc
    C ≤ 2 * T := hedge
    _ ≤ 2 * (4 * a * N) := mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = 8 * a * N := by ring

/-- Convert a counted-edge identity, edge recovery, and an anticommutator
energy estimate into the desired sensitivity inequality. The counting and energy
premises are explicit. -/
theorem sensitivity_bound_of_counting_energy {n d : ℕ}
    (f : Cube n → ℝ) (C T : ℝ)
    (hcount : averageSensitivity f = C / (2 : ℝ) ^ n)
    (hedge : C ≤ 2 * T)
    (henergy : T ≤ 4 * ((d : ℝ) * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ n) :
    averageSensitivity f ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  rw [hcount]
  simpa only [mul_assoc] using
    normalized_edge_bound (pow_pos (by norm_num : (0 : ℝ) < 2) n) hedge henergy

/-- The finite-matrix bound assuming an orthogonal projection family with
binomial multiplicities, coordinate tridiagonality, and low-block vanishing. -/
theorem sensitivity_bound_of_cube_grading {n d : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (P : Fin (n + 1) → Matrix (Cube n) (Cube n) ℂ)
    (hP : OrthogonalProjectionFamily P)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (htri : ∀ i : Fin n, BlockTridiagonal P (coordinateSignMatrix i))
    (hvanish : ∀ r s : Fin (n + 1), r.val + s.val < n - d →
      P s * signMatrix (fun x => fullParity x * f x) * P r = 0) :
    averageSensitivity f ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  classical
  let h : Cube n → ℝ := fun x => fullParity x * f x
  let H : Matrix (Cube n) (Cube n) ℂ := signMatrix h
  let M : Matrix (Cube n) (Cube n) ℂ := centeredGrading P
  have hh (x : Cube n) : h x = 1 ∨ h x = -1 := parity_twist_cases hf x
  have htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4 := by
    change hsNormSq (centeredGrading P) = _
    rw [hsNormSq_centeredGrading_trace hP]
    simp_rw [htrace]
    simpa only [mul_comm] using sum_choose_centered_sq n
  have hcoordinate (i : Fin n) :
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n := by
    simpa only [M, card_cube, Nat.cast_pow, Nat.cast_ofNat] using
      hsNormSq_centeredGrading_commutator_le_card hP (coordinateSignMatrix i)
        (htri i) (coordinateSignMatrix_unitary i)
  have hdistance :
      (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M := by
    rw [htotal]
    exact distance_energy_le_of_coordinate_commutator_bound M hcoordinate
  have hcap (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
    apply off_diagonal_sq_norm_le_quarter_of_commutator_bound M _ x y hxy
    intro i a b
    exact sq_norm_centeredGrading_commutator_entry_le_one hP (coordinateSignMatrix i)
      (htri i) (coordinateSignMatrix_unitary i) a b
  have hedge : ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * H + H * M) := edge_recovery M h hh htotal hdistance hcap
  have henergy : hsNormSq (M * H + H * M) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n :=
    hsNormSq_centeredGrading_anticommutator_le_of_trace n d P hP H
      (signMatrix_conjTranspose_mul h hh) (signMatrix_mul_conjTranspose h hh) htrace hvanish
  apply sensitivity_bound_of_counting_energy f ((orderedConstantEdges h).card : ℝ)
    (hsNormSq (M * H + H * M)) (averageSensitivity_eq_parity_edges hf) hedge
  simpa only [mul_assoc] using henergy

/-- The bound for a polynomial without cube zeros. The projection
family and both block-vanishing properties are constructed from its absolute
value, rather than retained as hypotheses. -/
theorem polynomialThreshold_averageSensitivity_le_of_nonzero {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x : Cube n, polynomialValue p x ≠ 0) :
    averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  let w : Cube n → ℝ := fun x => |polynomialValue p x|
  have hw (x : Cube n) : 0 < w x := abs_pos.mpr (hnz x)
  apply sensitivity_bound_of_cube_grading (polynomialThreshold p)
    (fun x => thresholdSign_cases (polynomialValue p x))
    (weightedProjectionMatrix w hw)
    (weightedProjectionMatrix_family w hw)
    (weightedProjectionMatrix_trace_re w hw)
  · intro i
    exact weightedProjectionMatrix_tridiagonal w hw i
  · intro r s hrs
    exact weightedProjectionMatrix_block_eq_zero_of_polynomial_degree p hp hd hnz r s hrs

/-- Every real multilinear polynomial of degree at most `d` has average
sensitivity at most `8*d*sqrt(n)`, including cube zeros under `sign(0)=1`.
The argument in fact covers all natural `n` and `d`. -/
theorem polynomialThreshold_averageSensitivity_le {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  obtain ⟨q, hq, hqd, hqnz, hqf⟩ := exists_nonzero_polynomial_same_threshold hp hd
  rw [← hqf]
  exact polynomialThreshold_averageSensitivity_le_of_nonzero q hq hqd hqnz

/-- The average-sensitivity bound for `1 ≤ d ≤ n`, without auxiliary
construction hypotheses. -/
theorem gotsmanLinialStatement : GotsmanLinialStatement := by
  intro n d _ _ _ p hp hd
  exact polynomialThreshold_averageSensitivity_le p hp hd

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
