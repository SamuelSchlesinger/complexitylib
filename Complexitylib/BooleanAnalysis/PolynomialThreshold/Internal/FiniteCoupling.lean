/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.ScalarIncrements
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# Gotsman--Linial: FiniteCoupling

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/FiniteCoupling.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
# A finite one-sided coupling estimate

This is a finite weighted probabilistic estimate. Equal
marginals are expressed as equality of the weighted expectations of every
real function. The increment bound is required only on the support of the
nonnegative probability weights.
-/

open scoped BigOperators

namespace BooleanAnalysis.PolynomialThreshold.Internal

variable {Ω : Type*} [Fintype Ω]

/-- Weighted Cauchy--Schwarz bounds the first absolute moment by a bound on
the second moment. Zero weights are allowed. -/
theorem weighted_abs_le_of_second_moment (w f : Ω → ℝ) (σ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hσ : 0 ≤ σ)
    (hsecond : ∑ i, w i * (f i) ^ 2 ≤ σ ^ 2) :
    ∑ i, w i * |f i| ≤ σ := by
  have hcs : (∑ i, w i * |f i|) ^ 2 ≤
      (∑ i, w i) * ∑ i, w i * (f i) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _
      exact hw i
    · intro i _
      exact mul_nonneg (hw i) (sq_nonneg (f i))
    · intro i _
      apply le_of_eq
      rw [mul_pow, sq_abs]
      ring
  rw [hprob, one_mul] at hcs
  have hnonneg : 0 ≤ ∑ i, w i * |f i| :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg (f i)))
  nlinarith

/-- A weighted mean-zero variable has absolute first moment twice the first
moment of its positive part. This identity does not need positivity of the weights. -/
theorem weighted_abs_eq_twice_positive_part (w z : Ω → ℝ)
    (hzero : ∑ i, w i * z i = 0) :
    ∑ i, w i * |z i| = 2 * ∑ i, w i * max (z i) 0 := by
  calc
    ∑ i, w i * |z i| =
        (∑ i, w i * |z i|) + ∑ i, w i * z i := by rw [hzero, add_zero]
    _ = ∑ i, (w i * |z i| + w i * z i) := by rw [Finset.sum_add_distrib]
    _ = ∑ i, 2 * (w i * max (z i) 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 ≤ z i
      · rw [abs_of_nonneg hi, max_eq_left hi]
        ring
      · have hi' : z i ≤ 0 := (lt_of_not_ge hi).le
        rw [abs_of_nonpos hi', max_eq_right hi']
        ring
    _ = 2 * ∑ i, w i * max (z i) 0 := by rw [Finset.mul_sum]

/-- The finite one-sided coupling lemma: identical marginals and an upper
bound `a` on `V - U` bound the mean square displacement by `8 * a * σ`.

The center `m` may be arbitrary. Taking it to be the common mean recovers the
variance bound with variance `σ²`; only the displayed second moment is used. -/
theorem finite_one_sided_coupling_bound (w U V : Ω → ℝ) (m σ a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hvariance : ∑ i, w i * (U i - m) ^ 2 = σ ^ 2)
    (hstep : ∀ i, w i ≠ 0 → V i - U i ≤ a) :
    ∑ i, w i * (U i - V i) ^ 2 ≤ 8 * a * σ := by
  let z : Ω → ℝ := fun i => couplingPotential m (V i) - couplingPotential m (U i)
  have hz : ∑ i, w i * z i = 0 := by
    simp only [z, mul_sub, Finset.sum_sub_distrib]
    rw [hsame (couplingPotential m), sub_self]
  have habs := weighted_abs_eq_twice_positive_part w z hz
  have hU : ∑ i, w i * |U i - m| ≤ σ :=
    weighted_abs_le_of_second_moment w (fun i => U i - m) σ hw hprob hσ hvariance.le
  have hV : ∑ i, w i * |V i - m| ≤ σ := by
    rw [← hsame (fun t => |t - m|)]
    exact hU
  have hpositive : ∑ i, w i * max (z i) 0 ≤ a * σ := by
    calc
      ∑ i, w i * max (z i) 0 ≤
          ∑ i, w i * (a / 2 * (|U i - m| + |V i - m|)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left
            (max_couplingPotential_increment_le m a (U i) (V i) ha (hstep i hi))
            (hw i)
      _ = a / 2 * ((∑ i, w i * |U i - m|) + ∑ i, w i * |V i - m|) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ a / 2 * (σ + σ) :=
        mul_le_mul_of_nonneg_left (add_le_add hU hV) (div_nonneg ha (by norm_num))
      _ = a * σ := by ring
  have hsquare : ∑ i, w i * (U i - V i) ^ 2 ≤ 4 * ∑ i, w i * |z i| := by
    calc
      ∑ i, w i * (U i - V i) ^ 2 ≤ ∑ i, w i * (4 * |z i|) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i)
        dsimp only [z]
        rw [abs_sub_comm]
        exact sq_sub_le_four_mul_abs_potential_sub m (U i) (V i)
      _ = 4 * ∑ i, w i * |z i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    ∑ i, w i * (U i - V i) ^ 2 ≤ 4 * ∑ i, w i * |z i| := hsquare
    _ = 8 * ∑ i, w i * max (z i) 0 := by rw [habs]; ring
    _ ≤ 8 * (a * σ) := mul_le_mul_of_nonneg_left hpositive (by norm_num)
    _ = 8 * a * σ := by ring

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
