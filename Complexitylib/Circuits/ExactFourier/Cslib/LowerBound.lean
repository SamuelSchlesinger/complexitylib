/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.ExactFourier.Cslib
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.DFT
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.Polynomial.Linearization

/-!
# Existing DFT lower bounds apply to the imported scalar model

The scalar signature is polynomial, so the library's local linearization
theorem supplies the coefficient certificate required by the DFT lower bound.
The one zero gate introduced by translation is charged explicitly.
-/

public section

namespace Complexity.ExactFourier

open Algebraic.Cutwidth.MultiOutput

/-- The exact scalar operations are polynomial in their argument slots. -/
theorem scalarInterpretation_isPolynomial : Polynomial.IsPolynomial scalarInterpretation := by
  intro op
  cases op with
  | zero => exact ⟨0, by intro x; simp [scalarInterpretation]⟩
  | add =>
      change ∃ q : MvPolynomial (Fin 2) ℂ, ∀ x, x 0 + x 1 = MvPolynomial.eval x q
      refine ⟨MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2), ?_⟩
      intro x
      simp
  | sub =>
      change ∃ q : MvPolynomial (Fin 2) ℂ, ∀ x, x 0 - x 1 = MvPolynomial.eval x q
      refine ⟨MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2), ?_⟩
      intro x
      simp
  | scale c =>
      change ∃ q : MvPolynomial (Fin 1) ℂ, ∀ x, c * x 0 = MvPolynomial.eval x q
      refine ⟨MvPolynomial.C c * MvPolynomial.X (0 : Fin 1), ?_⟩
      intro x
      simp

/-- The source DFT matrix is the matrix used by the existing lower-bound interface. -/
theorem fourierMatrix_eq_dft (n : ℕ) : fourierMatrix n = dft (zeta n) n := rfl

/-- All sufficiently large exact scalar Fourier circuits obey the library's linear lower bound. -/
theorem eventually_lt_cslib_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ C : Cslib.Circuits.Circuit scalarSignature n n,
      C.FanInAtMost 2 → C.Computes scalarInterpretation (fourierMatrix n).mulVec →
        (25 / 9 - ε) * n < C.size := by
  filter_upwards [Linear.eventually_lt_size_dft_twentyFive_div_nine hε,
    Filter.eventually_ge_atTop 1] with n hn hn1
  intro C hfan hC
  apply hn ℂ (zeta n) (Complex.isPrimitiveRoot_exp n (by lia)) scalarSignature C hfan
    (Polynomial.realization scalarInterpretation_isPolynomial C.program)
  intro i
  exact Polynomial.realization_output scalarInterpretation_isPolynomial C (fourierMatrix n) hC i

/-- Transferring the lower bound back charges the single additional zero gate. -/
theorem eventually_lt_source_size_add_one {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ C : Circuit n, C.Computes (fourierMatrix n) →
      (25 / 9 - ε) * n < C.size + 1 := by
  filter_upwards [eventually_lt_cslib_size hε] with n hn
  intro C hC
  simpa only [Circuit.size_toCslib, Nat.cast_add, Nat.cast_one] using
    hn C.toCslib C.toCslib_fanInAtMost hC.toCslib

/-- The source model itself inherits the asymptotic coefficient, absorbing the extra zero gate. -/
theorem eventually_lt_source_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ C : Circuit n, C.Computes (fourierMatrix n) →
      (25 / 9 - ε) * n < C.size := by
  have hh : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (ε / 2))
  have hgap := (div_lt_iff₀ hh).mp hN
  filter_upwards [eventually_lt_source_size_add_one hh,
    Filter.eventually_ge_atTop N] with n hn hNn
  intro C hC
  have hsize := hn C hC
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  nlinarith [mul_nonneg (sub_nonneg.mpr hNn') hh.le]

end Complexity.ExactFourier
