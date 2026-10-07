/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# Gotsman--Linial: BinomialMoments

Adapted from OpenAI's formalization of *Average Sensitivity of Polynomial Threshold
Functions* (25 September 2026), at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/GotsmanLinial/BinomialMoments.lean

The original Boolean-cube representation is used internally in this proof development;
`Complexitylib.BooleanAnalysis.PolynomialThreshold` transports the result to the
library's Fourier and influence API. Changes here adapt module visibility,
namespace names, formatting, and redundant simp attributes to complexitylib.
-/

@[expose] public section

namespace Complexity

/-!
Exact finite moments of the symmetric binomial weights. These identities provide
the grading multiplicities and the variance used in the finite coupling estimate.
No probabilistic assumptions or measures enter the statements.
-/

namespace BooleanAnalysis.PolynomialThreshold.Internal

open scoped BigOperators

/-- The normalizing denominator is positive, also when `n = 0`. -/
theorem binomialDenominator_pos (n : ℕ) : 0 < (2 : ℝ) ^ n :=
  pow_pos (by norm_num) n

theorem binomialDenominator_ne_zero (n : ℕ) : (2 : ℝ) ^ n ≠ 0 :=
  ne_of_gt (binomialDenominator_pos n)

/-- The real sum of one row of Pascal's triangle. -/
theorem sum_choose_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.sum_range_choose n

/-- Pascal recursion for an arbitrary real function of the binomial index. -/
theorem sum_choose_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) * f k) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f k) +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f (k + 1) :=
  Finset.sum_choose_succ_mul (fun k _ => f k) n

/-- The first raw binomial moment, with a formula valid at `n = 0`. -/
theorem sum_choose_mul_index_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) =
      (n : ℝ) * (2 : ℝ) ^ n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_choose_succ]
      simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [Finset.sum_add_distrib, ih, sum_choose_range]
      simp only [pow_succ]
      ring

/-- The second raw binomial moment, with a formula valid at `n = 0`. -/
theorem sum_choose_mul_index_sq_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 : ℝ) ^ n / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_choose_succ]
      have hshift :
          (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) =
            (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) +
              2 * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) +
              ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      rw [hshift, ih, sum_choose_mul_index_range, sum_choose_range]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring

/-- Exact centered second moment before dividing by `2^n`. -/
theorem sum_choose_centered_sq_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  calc
    _ = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) -
          (n : ℝ) * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) +
          ((n : ℝ) ^ 2 / 4) * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = _ := by
        rw [sum_choose_mul_index_sq_range, sum_choose_mul_index_range, sum_choose_range]
        ring

/-- The same total mass on the grading-index type. -/
theorem sum_choose (n : ℕ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ)) = (2 : ℝ) ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ))]
  exact sum_choose_range n

theorem sum_choose_mul_index (n : ℕ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ) * (k.val : ℝ)) =
      (n : ℝ) * (2 : ℝ) ^ n / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ) * (k : ℝ))]
  exact sum_choose_mul_index_range n

theorem sum_choose_mul_index_sq (n : ℕ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ) * (k.val : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 : ℝ) ^ n / 4 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ) * (k : ℝ) ^ 2)]
  exact sum_choose_mul_index_sq_range n

theorem sum_choose_centered_sq (n : ℕ) :
    (∑ k : Fin (n + 1),
      (n.choose k.val : ℝ) * ((k.val : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (n.choose k : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2)]
  exact sum_choose_centered_sq_range n

/-- The symmetric binomial probability weights, presented as a finite real function. -/
noncomputable def binomialWeight (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  (n.choose k.val : ℝ) / (2 : ℝ) ^ n

theorem binomialWeight_nonneg (n : ℕ) (k : Fin (n + 1)) :
    0 ≤ binomialWeight n k :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt (binomialDenominator_pos n))

theorem sum_binomialWeight (n : ℕ) : (∑ k : Fin (n + 1), binomialWeight n k) = 1 := by
  unfold binomialWeight
  rw [← Finset.sum_div, sum_choose, div_self (binomialDenominator_ne_zero n)]

theorem binomialWeight_mean (n : ℕ) :
    (∑ k : Fin (n + 1), binomialWeight n k * (k.val : ℝ)) = (n : ℝ) / 2 := by
  unfold binomialWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_choose_mul_index]
  field_simp [binomialDenominator_ne_zero n]

theorem binomialWeight_variance (n : ℕ) :
    (∑ k : Fin (n + 1), binomialWeight n k * ((k.val : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) / 4 := by
  unfold binomialWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_choose_centered_sq]
  field_simp [binomialDenominator_ne_zero n]

/-- The binomial coefficients are invariant under reflection about `n/2`. -/
theorem choose_reflect (n : ℕ) (k : Fin (n + 1)) :
    n.choose (n - k.val) = n.choose k.val :=
  Nat.choose_symm (Nat.le_of_lt_succ k.isLt)

theorem choose_rev (n : ℕ) (k : Fin (n + 1)) :
    n.choose k.rev.val = n.choose k.val := by
  simpa only [Fin.val_rev, Nat.add_sub_add_right] using choose_reflect n k

theorem binomialWeight_rev (n : ℕ) (k : Fin (n + 1)) :
    binomialWeight n k.rev = binomialWeight n k := by
  simp only [binomialWeight, choose_rev]

theorem index_rev_real (n : ℕ) (k : Fin (n + 1)) :
    (k.rev.val : ℝ) = (n : ℝ) - (k.val : ℝ) := by
  rw [Fin.val_rev, Nat.add_sub_add_right, Nat.cast_sub (Nat.le_of_lt_succ k.isLt)]

/-- Reflecting a binomial index preserves every real finite expectation. -/
theorem binomialWeight_reflect (n : ℕ) (φ : ℝ → ℝ) :
    (∑ k : Fin (n + 1), binomialWeight n k * φ ((n : ℝ) - (k.val : ℝ))) =
      ∑ k : Fin (n + 1), binomialWeight n k * φ (k.val : ℝ) := by
  have h := Equiv.sum_comp (Fin.revPerm (n := n + 1))
    (fun k : Fin (n + 1) => binomialWeight n k * φ (k.val : ℝ))
  change (∑ k : Fin (n + 1), binomialWeight n k.rev * φ (k.rev.val : ℝ)) = _ at h
  simpa only [binomialWeight_rev, index_rev_real] using h

/-- Standard deviation corresponding to the preceding finite variance identity. -/
theorem binomialSigma_sq (n : ℕ) : (Real.sqrt (n : ℝ) / 2) ^ 2 = (n : ℝ) / 4 := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  norm_num

theorem binomialSigma_nonneg (n : ℕ) : 0 ≤ Real.sqrt (n : ℝ) / 2 :=
  div_nonneg (Real.sqrt_nonneg _) (by norm_num)

end BooleanAnalysis.PolynomialThreshold.Internal

end Complexity
