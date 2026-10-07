/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Gotsman--Linial: ScalarIncrements

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/ScalarIncrements.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# Scalar inequalities for the one-sided coupling estimate

The increasing function `couplingPotential m t = (t-m)|t-m|/2` controls
squared distances from below and has a trapezoidal increment bound from above.
All arguments here are algebraic, by splitting according to the positions of
the endpoints relative to the center `m`.
-/

namespace BooleanAnalysis.PolynomialThreshold.Internal

/-- The scalar potential used in the one-sided coupling argument. -/
noncomputable def couplingPotential (m t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (t - m) * |t - m|

@[simp] theorem couplingPotential_self (m : ℝ) : couplingPotential m m = 0 := by
  simp [couplingPotential]

/-- Both increment inequalities hold even when the endpoints coincide. -/
theorem couplingPotential_increment_bounds (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    (v - u) ^ 2 / 4 ≤ couplingPotential m v - couplingPotential m u ∧
      couplingPotential m v - couplingPotential m u ≤
        (v - u) / 2 * (|u - m| + |v - m|) := by
  by_cases hum : u ≤ m
  · by_cases hvm : v ≤ m
    · simp only [couplingPotential, abs_of_nonpos (sub_nonpos.mpr hum),
        abs_of_nonpos (sub_nonpos.mpr hvm)]
      constructor
      · nlinarith [sq_nonneg (v - u),
          mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hvm)]
      · nlinarith
    · have hmv : m ≤ v := (not_le.mp hvm).le
      simp only [couplingPotential, abs_of_nonpos (sub_nonpos.mpr hum),
        abs_of_nonneg (sub_nonneg.mpr hmv)]
      constructor
      · nlinarith [sq_nonneg (u + v - 2 * m)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hum) (sub_nonneg.mpr hmv)]
  · have hmu : m ≤ u := (not_le.mp hum).le
    have hmv : m ≤ v := hmu.trans huv
    simp only [couplingPotential, abs_of_nonneg (sub_nonneg.mpr hmu),
      abs_of_nonneg (sub_nonneg.mpr hmv)]
    constructor
    · nlinarith [sq_nonneg (v - u),
        mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hmu)]
    · nlinarith

theorem couplingPotential_increment_lower (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    (v - u) ^ 2 / 4 ≤ couplingPotential m v - couplingPotential m u :=
  (couplingPotential_increment_bounds m huv).1

theorem couplingPotential_increment_upper (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    couplingPotential m v - couplingPotential m u ≤
      (v - u) / 2 * (|u - m| + |v - m|) :=
  (couplingPotential_increment_bounds m huv).2

theorem monotone_couplingPotential (m : ℝ) : Monotone (couplingPotential m) := by
  intro u v huv
  have h := couplingPotential_increment_lower m huv
  nlinarith [sq_nonneg (v - u)]

theorem strictMono_couplingPotential (m : ℝ) : StrictMono (couplingPotential m) := by
  intro u v huv
  have h := couplingPotential_increment_lower m huv.le
  have hs := mul_pos (sub_pos.mpr huv) (sub_pos.mpr huv)
  nlinarith

@[simp] theorem couplingPotential_le_iff (m u v : ℝ) :
    couplingPotential m u ≤ couplingPotential m v ↔ u ≤ v :=
  (strictMono_couplingPotential m).le_iff_le

@[simp] theorem couplingPotential_lt_iff (m u v : ℝ) :
    couplingPotential m u < couplingPotential m v ↔ u < v :=
  (strictMono_couplingPotential m).lt_iff_lt

@[simp] theorem couplingPotential_eq_iff (m u v : ℝ) :
    couplingPotential m u = couplingPotential m v ↔ u = v :=
  (strictMono_couplingPotential m).injective.eq_iff

theorem couplingPotential_sub_nonneg_iff (m u v : ℝ) :
    0 ≤ couplingPotential m v - couplingPotential m u ↔ u ≤ v := by
  rw [sub_nonneg, couplingPotential_le_iff]

theorem couplingPotential_sub_pos_iff (m u v : ℝ) :
    0 < couplingPotential m v - couplingPotential m u ↔ u < v := by
  rw [sub_pos, couplingPotential_lt_iff]

theorem abs_couplingPotential_sub_of_le (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    |couplingPotential m v - couplingPotential m u| =
      couplingPotential m v - couplingPotential m u :=
  abs_of_nonneg ((couplingPotential_sub_nonneg_iff m u v).mpr huv)

/-- The pointwise lower bound in the coupling argument, without ordering the
two real variables. -/
theorem sq_sub_le_four_mul_abs_potential_sub (m u v : ℝ) :
    (u - v) ^ 2 ≤ 4 * |couplingPotential m u - couplingPotential m v| := by
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm, abs_couplingPotential_sub_of_le m huv]
    have h := couplingPotential_increment_lower m huv
    nlinarith
  · rw [abs_couplingPotential_sub_of_le m hvu]
    have h := couplingPotential_increment_lower m hvu
    nlinarith

/-- An upper bound for the positive part of a potential increment under a
one-sided bound on the original increment. -/
theorem max_couplingPotential_increment_le (m a u v : ℝ)
    (ha : 0 ≤ a) (hstep : v - u ≤ a) :
    max (couplingPotential m v - couplingPotential m u) 0 ≤
      a / 2 * (|u - m| + |v - m|) := by
  have hs : 0 ≤ |u - m| + |v - m| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  by_cases huv : u ≤ v
  · rw [max_eq_left ((couplingPotential_sub_nonneg_iff m u v).mpr huv)]
    have h := couplingPotential_increment_upper m huv
    have hp := mul_nonneg (sub_nonneg.mpr hstep) hs
    nlinarith
  · have hvu : v ≤ u := (not_le.mp huv).le
    rw [max_eq_right (sub_nonpos.mpr ((monotone_couplingPotential m) hvu))]
    nlinarith [mul_nonneg ha hs]

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
