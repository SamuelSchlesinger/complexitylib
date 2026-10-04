/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite

/-!
# Weight certificates from one-sided Boolean bias

A Boolean message with true probability at most `p ≤ 1/2` has a normalized
weight certificate of cost `binEntropy p`. No independence is required.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

/-- A one-sided bound on the number of true messages gives a binary-entropy cost. -/
noncomputable def WeightBound.ofTrueCountLE {X : Type*} [Fintype X]
    (bit : X → Bool) {p : ℝ} (positive : 0 < p) (half : p ≤ 1 / 2)
    (count : ((Finset.univ.filter fun x => bit x = true).card : ℝ) ≤
      p * Fintype.card X) : WeightBound bit (Real.binEntropy p) where
  weight b := if b then p else 1 - p
  nonneg b := by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  mass := by simp
  positive x := by cases bit x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  log_bound := by
    have complement : 0 < 1 - p := by linarith
    have logs : Real.log p ≤ Real.log (1 - p) :=
      Real.log_le_log positive (by linarith)
    have point (x : X) :
        Real.log (if bit x then p else 1 - p) = Real.log (1 - p) +
          (if bit x = true then (1 : ℝ) else 0) * (Real.log p - Real.log (1 - p)) := by
      cases bit x <;> simp
    have total : (∑ x, Real.log (if bit x then p else 1 - p)) =
        Fintype.card X * Real.log (1 - p) +
          ((Finset.univ.filter fun x => bit x = true).card : ℝ) *
            (Real.log p - Real.log (1 - p)) := by
      simp_rw [point]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp
    have entropy : Real.binEntropy p =
        -p * Real.log p - (1 - p) * Real.log (1 - p) := by
      rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
      simp only [Real.negMulLog_def]
      ring
    rw [total, entropy]
    nlinarith [mul_nonneg (sub_nonneg.mpr count) (sub_nonneg.mpr logs)]

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
