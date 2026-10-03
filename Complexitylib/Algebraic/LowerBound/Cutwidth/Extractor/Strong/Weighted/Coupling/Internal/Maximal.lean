/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Internal.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite maximal coupling

Place the common mass `min(p,q)` on the diagonal and couple the two remaining
nonnegative weights by their product divided by their common total mass.
The two residual weights have disjoint supports, so the residual coupling
is entirely off the diagonal. Zero residual mass is covered by the
zero-mass cancellation lemma.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem exists_maximal_coupling {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q) :
    ∃ r : α × α → ℝ, IsProbabilityWeight r ∧
      (∀ a, ∑ b, r (a, b) = p a) ∧ (∀ b, ∑ a, r (a, b) = q b) ∧
        (∑ z with z.1 ≠ z.2, r z) = weightDist p q := by
  let d (a : α) := min (p a) (q a)
  let u (a : α) := p a - d a
  let v (a : α) := q a - d a
  let mass := ∑ a, u a
  have d_nonneg (a : α) : 0 ≤ d a := le_min (hp.1 a) (hq.1 a)
  have u_nonneg (a : α) : 0 ≤ u a := sub_nonneg.mpr (min_le_left _ _)
  have v_nonneg (a : α) : 0 ≤ v a := sub_nonneg.mpr (min_le_right _ _)
  have mass_nonneg : 0 ≤ mass := Finset.sum_nonneg fun a _ => u_nonneg a
  have same_mass : (∑ a, v a) = mass := by
    simp only [v, u, mass, Finset.sum_sub_distrib, hp.2, hq.2]
  have row_residual (a : α) : u a * mass / mass = u a :=
    nonnegWeight_mul_mass_div u u_nonneg a
  have column_residual (b : α) : mass * v b / mass = v b := by
    rw [mul_comm mass, ← same_mass]
    exact nonnegWeight_mul_mass_div v v_nonneg b
  let r (z : α × α) := (if z.1 = z.2 then d z.1 else 0) + u z.1 * v z.2 / mass
  have nonnegative (z : α × α) : 0 ≤ r z := by
    have diagonal : 0 ≤ if z.1 = z.2 then d z.1 else 0 := by
      split
      · exact d_nonneg z.1
      · exact le_refl 0
    exact add_nonneg diagonal
      (div_nonneg (mul_nonneg (u_nonneg z.1) (v_nonneg z.2)) mass_nonneg)
  have row (a : α) : ∑ b, r (a, b) = p a := by
    simp only [r, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    rw [same_mass, row_residual]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    dsimp only [u]
    ring
  have column (b : α) : ∑ a, r (a, b) = q b := by
    simp only [r, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    change (∑ a, if a = b then d a else 0) + mass * v b / mass = q b
    rw [column_residual]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    dsimp only [v]
    ring
  have total : ∑ z, r z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [row, hp.2]
  refine ⟨r, ⟨nonnegative, total⟩, row, column, ?_⟩
  have off_diagonal (a b : α) :
      (if a ≠ b then r (a, b) else 0) = u a * v b / mass := by
    by_cases equal : a = b
    · subst b
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      rw [show u a * v a = 0 from common_residual_mul_self_eq_zero (p a) (q a)]
      simp
    · simp only [equal, ne_eq, not_false_eq_true, ↓reduceIte, r, zero_add]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [off_diagonal, ← Finset.sum_div, ← Finset.mul_sum, same_mass, row_residual]
  exact sum_common_residual_eq_weightDist hp hq

end Algebraic.Cutwidth.Extractor.Internal
