/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Correlation bounds imply threshold-weight bounds

If every feature has correlation at most `ε` with a target, any linear
combination representing the target with margin `γ` must have coefficient
weight at least `γ / ε`. This elementary duality argument provides the
threshold-weight step for consequences of OpenAI's depth-three circuit result:
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Beyond-the-Square-Root-Exponent-for-Depth-Three-Boolean-Circuits-September-23-2026

The result is stated for arbitrary finite domains and real-valued features,
so it applies to CNF indicators and other feature classes. A bias is another
feature, namely the constant function one, and needs its own correlation bound.
The conclusion bounds the sum of absolute coefficient values. It does not
bound the number of arbitrary-weight gates or the binary encoding length of
their coefficients.
-/

public section

namespace Complexity.BooleanAnalysis

open scoped BigOperators

/-- Small correlations force large coefficient weight for any representation
with a uniform signed margin. The margin and correlation bounds are explicit. -/
theorem margin_le_correlation_mul_weight
    {X J : Type*} [Fintype X] [Nonempty X] [Fintype J]
    (g : X → ℝ) (H : J → X → ℝ) (a : J → ℝ) (ε γ : ℝ)
    (hcorr : ∀ j, |𝔼 x, g x * H j x| ≤ ε)
    (hmargin : ∀ x, γ ≤ g x * ∑ j, a j * H j x) :
    γ ≤ ε * ∑ j, |a j| := by
  calc
    γ ≤ 𝔼 x, g x * ∑ j, a j * H j x :=
      Finset.le_expect Finset.univ_nonempty (fun x _ => hmargin x)
    _ = ∑ j, a j * (𝔼 x, g x * H j x) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ ≤ ∑ j, |a j| * ε := by
      apply Finset.sum_le_sum
      intro j _
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcorr j) (abs_nonneg _)
    _ = ε * ∑ j, |a j| := by rw [← Finset.sum_mul, mul_comm]

/-- A margin-one threshold representation has weight at least the reciprocal
of the common correlation bound. -/
theorem threshold_weight_lower_bound
    {X J : Type*} [Fintype X] [Nonempty X] [Fintype J]
    (g : X → ℝ) (H : J → X → ℝ) (a : J → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hcorr : ∀ j, |𝔼 x, g x * H j x| ≤ ε)
    (hmargin : ∀ x, 1 ≤ g x * ∑ j, a j * H j x) :
    1 / ε ≤ ∑ j, |a j| := by
  apply (div_le_iff₀ hε).mpr
  simpa only [mul_comm] using margin_le_correlation_mul_weight g H a ε 1 hcorr hmargin

end Complexity.BooleanAnalysis
