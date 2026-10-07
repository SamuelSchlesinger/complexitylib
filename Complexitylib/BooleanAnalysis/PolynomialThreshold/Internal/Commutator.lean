/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.ProjectionBlocks
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic

/-!
# Gotsman--Linial: Commutator

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/Commutator.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Entry bounds for a tridiagonal grading commutator

All norms here are norms of individual complex entries.  No default
norm on a matrix is used.  A complete orthogonal family defines a phase
unitary with eigenvalues `I^k`.  For a tridiagonal operator the commutator is
the difference of two unitary conjugates divided by `2 I`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace BooleanAnalysis.PolynomialThreshold.Internal

section SpectralMultiplier

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A complex spectral multiplier for a finite family of projections. -/
def spectralMultiplier (P : κ → Matrix ι ι ℂ) (a : κ → ℂ) : Matrix ι ι ℂ :=
  ∑ k, a k • P k

variable (P : κ → Matrix ι ι ℂ)
variable (hmul : ∀ r s, P r * P s = if r = s then P r else 0)
include hmul

theorem spectralMultiplier_mul_projection (a : κ → ℂ) (r : κ) :
    spectralMultiplier P a * P r = a r • P r := by
  classical
  simp [spectralMultiplier, Finset.sum_mul, hmul]

theorem projection_mul_spectralMultiplier (a : κ → ℂ) (r : κ) :
    P r * spectralMultiplier P a = a r • P r := by
  classical
  simp [spectralMultiplier, Finset.mul_sum, hmul]

theorem spectralMultiplier_mul (a b : κ → ℂ) :
    spectralMultiplier P a * spectralMultiplier P b =
      spectralMultiplier P (fun k => a k * b k) := by
  change spectralMultiplier P a * (∑ k, b k • P k) = _
  rw [Finset.mul_sum]
  simp only [mul_smul_comm, spectralMultiplier_mul_projection P hmul, smul_smul]
  simp only [spectralMultiplier, mul_comm]

omit hmul [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem star_spectralMultiplier (hstar : ∀ k, star (P k) = P k) (a : κ → ℂ) :
    star (spectralMultiplier P a) = spectralMultiplier P (fun k => star (a k)) := by
  simp only [spectralMultiplier, star_sum, star_smul, hstar]

theorem spectralMultiplier_unitary
    (hstar : ∀ k, star (P k) = P k) (hsum : ∑ k, P k = 1)
    (a : κ → ℂ) (ha : ∀ k, a k * star (a k) = 1) :
    spectralMultiplier P a ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_spectralMultiplier P hstar,
    spectralMultiplier_mul P hmul]
  simpa only [spectralMultiplier, ha, one_smul] using hsum

theorem spectralMultiplier_sandwich_block (a b : κ → ℂ)
    (Z : Matrix ι ι ℂ) (r s : κ) :
    P s * (spectralMultiplier P a * Z * spectralMultiplier P b) * P r =
      (a s * b r) • (P s * Z * P r) := by
  calc
    _ = ((P s * spectralMultiplier P a) * Z) *
        (spectralMultiplier P b * P r) := by simp only [mul_assoc]
    _ = ((a s • P s) * Z) * (b r • P r) := by
      rw [projection_mul_spectralMultiplier P hmul,
        spectralMultiplier_mul_projection P hmul]
    _ = _ := by simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem spectralMultiplier_commutator_block (a : κ → ℂ)
    (Z : Matrix ι ι ℂ) (r s : κ) :
    P s * (spectralMultiplier P a * Z - Z * spectralMultiplier P a) * P r =
      (a s - a r) • (P s * Z * P r) := by
  have hleft : P s * (spectralMultiplier P a * Z) * P r =
      a s • (P s * Z * P r) := by
    rw [← mul_assoc (P s) (spectralMultiplier P a) Z,
      projection_mul_spectralMultiplier P hmul]
    simp only [smul_mul_assoc]
  have hright : P s * (Z * spectralMultiplier P a) * P r =
      a r • (P s * Z * P r) := by
    calc
      _ = (P s * Z) * (spectralMultiplier P a * P r) := by simp only [mul_assoc]
      _ = _ := by rw [spectralMultiplier_mul_projection P hmul, mul_smul_comm]
  rw [mul_sub, sub_mul, hleft, hright, sub_smul]

omit hmul [DecidableEq κ] in
theorem spectral_blocks_reconstruct (hsum : ∑ k, P k = 1) (B : Matrix ι ι ℂ) :
    (∑ s, ∑ r, P s * B * P r) = B := by
  simp only [← Finset.mul_sum, hsum, mul_one, ← Finset.sum_mul, one_mul]

omit hmul [DecidableEq κ] in
theorem spectral_blocks_ext (hsum : ∑ k, P k = 1) (A B : Matrix ι ι ℂ)
    (h : ∀ r s, P s * A * P r = P s * B * P r) : A = B := by
  rw [← spectral_blocks_reconstruct P hsum A, ← spectral_blocks_reconstruct P hsum B]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => h r s

end SpectralMultiplier

theorem I_pow_mul_star (k : ℕ) : Complex.I ^ k * star (Complex.I ^ k) = 1 := by
  rw [Complex.star_def, Complex.mul_conj']
  simp

theorem phase_coeff_adjacent (r s : ℕ) (h₁ : s ≤ r + 1) (h₂ : r ≤ s + 1) :
    Complex.I ^ s * star (Complex.I ^ r) - star (Complex.I ^ s) * Complex.I ^ r =
      (2 * Complex.I) * ((s : ℂ) - (r : ℂ)) := by
  have hcases : s = r ∨ s = r + 1 ∨ r = s + 1 := by omega
  rcases hcases with h | h | h
  · subst s
    simp [mul_comm]
  · subst s
    simp only [pow_succ, star_mul, Complex.star_def, Complex.conj_I, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = (2 * Complex.I) * (Complex.I ^ r * star (Complex.I ^ r)) := by
        simp only [Complex.star_def]
        ring
      _ = _ := by rw [I_pow_mul_star]; ring
  · subst r
    simp only [pow_succ, star_mul, Complex.star_def, Complex.conj_I, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = -(2 * Complex.I) * (Complex.I ^ s * star (Complex.I ^ s)) := by
        simp only [Complex.star_def]
        ring
      _ = _ := by rw [I_pow_mul_star]; ring

/-- The difference of two unitary matrices, divided by `2 I`, has entries
of modulus at most one. -/
theorem entry_norm_le_one_of_two_unitaries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C U V : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (h : (2 * Complex.I) • C = U - V) (x y : ι) : ‖C x y‖ ≤ 1 := by
  have heq := congrArg (fun A : Matrix ι ι ℂ => A x y) h
  have hn : (2 : ℝ) * ‖C x y‖ = ‖U x y - V x y‖ := by
    simpa [norm_mul] using congrArg norm heq
  have htri := norm_sub_le (U x y) (V x y)
  have hu₂ := sq_norm_entry_le_one_of_unitary U hU.1 x y
  have hv₂ := sq_norm_entry_le_one_of_unitary V hV.1 x y
  have hu : ‖U x y‖ ≤ 1 := by nlinarith [norm_nonneg (U x y)]
  have hv : ‖V x y‖ ≤ 1 := by nlinarith [norm_nonneg (V x y)]
  linarith

section GradingCommutator

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Fin (n + 1) → Matrix ι ι ℂ}

/-- The spectral phase `I^k` of the degree grading. -/
def gradingPhase (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  spectralMultiplier P fun k => Complex.I ^ k.val

theorem gradingPhase_unitary (hP : OrthogonalProjectionFamily P) :
    gradingPhase P ∈ Matrix.unitaryGroup ι ℂ := by
  exact spectralMultiplier_unitary P hP.mul_eq_ite (fun k => (hP.selfAdjoint k).star_eq)
    hP.sum_eq_one _ (fun k => I_pow_mul_star k.val)

/-- Tridiagonality means that blocks at grading distance greater than one vanish. -/
def BlockTridiagonal (P : Fin (n + 1) → Matrix ι ι ℂ) (Z : Matrix ι ι ℂ) : Prop :=
  ∀ r s : Fin (n + 1), (r.val + 1 < s.val ∨ s.val + 1 < r.val) →
    P s * Z * P r = 0

/-- Two opposite phase conjugations differ by `2 I` times the grading commutator. -/
theorem grading_commutator_phase_identity (hP : OrthogonalProjectionFamily P)
    (Z : Matrix ι ι ℂ) (htri : BlockTridiagonal P Z) :
    (2 * Complex.I) • (degreeGrading P * Z - Z * degreeGrading P) =
      gradingPhase P * Z * star (gradingPhase P) -
        star (gradingPhase P) * Z * gradingPhase P := by
  apply projection_block_ext hP
  intro r s
  rw [Matrix.mul_smul, Matrix.smul_mul, degreeGrading, projection_commutator hP,
    Matrix.mul_sub, Matrix.sub_mul]
  simp only [gradingPhase,
    star_spectralMultiplier P (fun k => (hP.selfAdjoint k).star_eq)]
  rw [spectralMultiplier_sandwich_block P hP.mul_eq_ite,
    spectralMultiplier_sandwich_block P hP.mul_eq_ite]
  by_cases hfar : r.val + 1 < s.val ∨ s.val + 1 < r.val
  · simp only [htri r s hfar, smul_zero, sub_self]
  · have hsr : s.val ≤ r.val + 1 := by omega
    have hrs : r.val ≤ s.val + 1 := by omega
    rw [← sub_smul, smul_smul, phase_coeff_adjacent r.val s.val hsr hrs]
    simp

/-- Every entry of the tridiagonal degree commutator has modulus at most one. -/
theorem norm_degreeGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(degreeGrading P * Z - Z * degreeGrading P) x y‖ ≤ 1 := by
  have hW := gradingPhase_unitary hP
  have hWstar := Unitary.star_mem hW
  have hU : gradingPhase P * Z * star (gradingPhase P) ∈ Matrix.unitaryGroup ι ℂ :=
    (Matrix.unitaryGroup ι ℂ).mul_mem ((Matrix.unitaryGroup ι ℂ).mul_mem hW hZ) hWstar
  have hV : star (gradingPhase P) * Z * gradingPhase P ∈ Matrix.unitaryGroup ι ℂ :=
    (Matrix.unitaryGroup ι ℂ).mul_mem ((Matrix.unitaryGroup ι ℂ).mul_mem hWstar hZ) hW
  exact entry_norm_le_one_of_two_unitaries _ _ _ hU hV
    (grading_commutator_phase_identity hP Z htri) x y

/-- The Hilbert--Schmidt commutator bound is a consequence of block Parseval
and the fact that each nonzero block has grading distance at most one. -/
theorem hsNormSq_degreeGrading_commutator_le
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) :
    hsNormSq (degreeGrading P * Z - Z * degreeGrading P) ≤ hsNormSq Z := by
  rw [degreeGrading, hsNormSq_commutator hP, hsNormSq_block_parseval hP Z]
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro s _
  by_cases hfar : r.val + 1 < s.val ∨ s.val + 1 < r.val
  · simp only [htri r s hfar, hsNormSq_zero, mul_zero, le_refl]
  · have hsr : (s.val : ℝ) ≤ (r.val : ℝ) + 1 := by
      exact_mod_cast (show s.val ≤ r.val + 1 by omega)
    have hrs : (r.val : ℝ) ≤ (s.val : ℝ) + 1 := by
      exact_mod_cast (show r.val ≤ s.val + 1 by omega)
    have hsq : ((s.val : ℝ) - (r.val : ℝ)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    exact (mul_le_mul_of_nonneg_right hsq (hsNormSq_nonneg _)).trans_eq (one_mul _)

theorem hsNormSq_degreeGrading_commutator_le_card
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ) :
    hsNormSq (degreeGrading P * Z - Z * degreeGrading P) ≤ Fintype.card ι := by
  calc
    _ ≤ hsNormSq Z := hsNormSq_degreeGrading_commutator_le hP Z htri
    _ = _ := hsNormSq_of_unitary Z hZ.1

/-- Centering the grading does not change its commutator. -/
theorem centeredGrading_commutator_eq (hP : OrthogonalProjectionFamily P)
    (Z : Matrix ι ι ℂ) :
    centeredGrading P * Z - Z * centeredGrading P =
      degreeGrading P * Z - Z * degreeGrading P := by
  rw [centeredGrading_eq hP]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

theorem norm_centeredGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(centeredGrading P * Z - Z * centeredGrading P) x y‖ ≤ 1 := by
  rw [centeredGrading_commutator_eq hP]
  exact norm_degreeGrading_commutator_entry_le_one hP Z htri hZ x y

theorem sq_norm_centeredGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(centeredGrading P * Z - Z * centeredGrading P) x y‖ ^ 2 ≤ 1 := by
  rw [sq_le_one_iff₀ (norm_nonneg _)]
  exact norm_centeredGrading_commutator_entry_le_one hP Z htri hZ x y

theorem hsNormSq_centeredGrading_commutator_le_card
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ) :
    hsNormSq (centeredGrading P * Z - Z * centeredGrading P) ≤ Fintype.card ι := by
  rw [centeredGrading_commutator_eq hP]
  exact hsNormSq_degreeGrading_commutator_le_card hP Z htri hZ

end GradingCommutator

end BooleanAnalysis.PolynomialThreshold.Internal

end

end Complexity
