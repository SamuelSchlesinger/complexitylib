/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.ExactFourier.Defs
public import Complexitylib.Circuits.ExactFourier.Internal.Main
public import Complexitylib.Circuits.ExactFourier.Cslib.LowerBound

/-!
# Exact Fourier circuits below every fixed multiple of n log n

OpenAI's result supplies arbitrarily large transform sizes with exact scalar
circuits of size below `c * n * log₂ n`, for each positive `c`. Its equivalent
minimum-size statement is a liminf of zero. The conclusion is about a cofinal
set of sizes; it does not assert a uniform bound at every sufficiently large size.

The source charges each addition, subtraction, and multiplication by an arbitrary
complex scalar. The CSLib translation preserves those operations and adds one
zero gate. Its coefficients are unrestricted; this is not a bounded-coefficient
or bit-complexity model. Source and provenance are recorded in `docs/OpenAIMath.md`.

The additional lower-bound corollaries use complexitylib's existing DFT results.
They place the imported circuits and the library's lower bounds in one model,
without a claim of new mathematical priority.
-/

public section

namespace Complexity.ExactFourier

/-- The literal minimum scalar gate count, normalized by `n * log₂ n`, has liminf zero. -/
theorem minimumSize_normalized_liminf :
    Filter.liminf (fun n : ℕ => (minimumSize n : ℝ) / (n * Real.logb 2 n)) Filter.atTop = 0 :=
  main_liminf

/-- At arbitrarily large sizes, exact Fourier circuits beat any fixed `n * log₂ n` coefficient. -/
theorem exists_small_fourier_circuit (c : ℝ) (hc : 0 < c) (N₀ : ℕ) :
    ∃ n, N₀ ≤ n ∧ 2 ≤ n ∧ ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * n * Real.logb 2 n := by
  obtain ⟨n, hn, C, hC, hs⟩ := main_theorem c hc (max N₀ 2) (le_max_right _ _)
  exact ⟨n, (le_max_left _ _).trans hn, (le_max_right _ _).trans hn, C, hC, hs⟩

/-- The same cofinal improvement holds for ordinary CSLib gate count. -/
theorem exists_small_cslib_fourier_circuit (c : ℝ) (hc : 0 < c) (N₀ : ℕ) :
    ∃ n, N₀ ≤ n ∧ 2 ≤ n ∧ ∃ C : Cslib.Circuits.Circuit scalarSignature n n,
      C.FanInAtMost 2 ∧ C.Computes scalarInterpretation (fourierMatrix n).mulVec ∧
        (C.size : ℝ) < c * n * Real.logb 2 n := by
  have hhalf : 0 < c / 2 := half_pos hc
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (c / 2))
  obtain ⟨n, hn, hn2, C, hC, hs⟩ :=
    exists_small_fourier_circuit (c / 2) hhalf (max N₀ N)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_max_right N₀ N).trans hn
  have hgap : 1 < (c / 2) * (n : ℝ) := by
    have h := (div_lt_iff₀ hhalf).mp hN
    nlinarith [mul_nonneg (sub_nonneg.mpr hNn) hhalf.le]
  have hlog : 1 ≤ Real.logb 2 (n : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn2 : (2 : ℝ) ≤ n)
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  have hle : (c / 2) * (n : ℝ) ≤ (c / 2) * n * Real.logb 2 n :=
    le_mul_of_one_le_right (by positivity) hlog
  refine ⟨n, (le_max_left _ _).trans hn, hn2, C.toCslib,
    C.toCslib_fanInAtMost, hC.toCslib, ?_⟩
  rw [Circuit.size_toCslib, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The imported upper bounds coexist with the library's linear lower bound in one model. -/
theorem exists_cslib_fourier_between_bounds (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (N₀ : ℕ) :
    ∃ n, N₀ ≤ n ∧ ∃ C : Cslib.Circuits.Circuit scalarSignature n n,
      C.Computes scalarInterpretation (fourierMatrix n).mulVec ∧
        (25 / 9 - ε) * n < C.size ∧ (C.size : ℝ) < c * n * Real.logb 2 n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_lt_cslib_size hε)
  obtain ⟨n, hn, _, C, hfan, hC, hs⟩ :=
    exists_small_cslib_fourier_circuit c hc (max N₀ N)
  exact ⟨n, (le_max_left _ _).trans hn, C, hC,
    hN n ((le_max_right _ _).trans hn) C hfan hC, hs⟩

/-- No positive `n * log₂ n` lower bound holds eventually for unrestricted scalar circuits. -/
theorem not_eventually_le_cslib_size (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n : ℕ in Filter.atTop, ∀ C : Cslib.Circuits.Circuit scalarSignature n n,
      C.FanInAtMost 2 → C.Computes scalarInterpretation (fourierMatrix n).mulVec →
        c * n * Real.logb 2 n ≤ C.size := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨n, hn, _, C, hfan, hC, hs⟩ := exists_small_cslib_fourier_circuit c hc N
  exact (not_lt_of_ge (hN n hn C hfan hC)) hs

end Complexity.ExactFourier
