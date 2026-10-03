/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Common mass and zero-mass fibers

The positive residual after removing pointwise common mass equals total
variation distance. Nonnegative zero-mass fibers vanish pointwise, making
the normalized residual and conditional-kernel formulas valid at zero mass.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem nonnegWeight_eq_zero_of_mass_zero {α : Type*} [Fintype α]
    {p : α → ℝ} (nonnegative : ∀ x, 0 ≤ p x) (mass : ∑ x, p x = 0) (x : α) :
    p x = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => nonnegative x)).mp mass x (Finset.mem_univ x)

theorem nonnegWeight_mul_mass_div {α : Type*} [Fintype α] (p : α → ℝ)
    (nonnegative : ∀ x, 0 ≤ p x) (x : α) :
    p x * (∑ y, p y) / (∑ y, p y) = p x := by
  by_cases zero : ∑ y, p y = 0
  · rw [nonnegWeight_eq_zero_of_mass_zero nonnegative zero x]
    simp
  · exact mul_div_cancel_right₀ _ zero

theorem sum_common_residual_eq_weightDist {α : Type*} [Fintype α]
    {p q : α → ℝ} (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q) :
    ∑ x, (p x - min (p x) (q x)) = weightDist p q := by
  have equal : (∑ x, (q x - min (p x) (q x))) =
      ∑ x, (p x - min (p x) (q x)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp.2, hq.2]
  have point (x : α) : |p x - q x| =
      (p x - min (p x) (q x)) + (q x - min (p x) (q x)) := by
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [weightDist]
  simp_rw [point]
  rw [Finset.sum_add_distrib, equal]
  ring

theorem common_residual_mul_self_eq_zero (a b : ℝ) :
    (a - min a b) * (b - min a b) = 0 := by
  rcases le_total a b with h | h
  · simp only [min_eq_left h, sub_self, zero_mul]
  · simp only [min_eq_right h, sub_self, mul_zero]

end Algebraic.Cutwidth.Extractor.Internal
