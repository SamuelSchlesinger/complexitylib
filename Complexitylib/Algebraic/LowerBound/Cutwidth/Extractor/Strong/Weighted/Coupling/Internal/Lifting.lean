/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Internal.Maximal
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

/-!
# Lifting a marginal coupling through a correlated joint law

Given the old joint weight on `(a,b)` and a coupling of its first marginal
with a new `a`, retain the conditional distribution of `b` given the old
`a`. The resulting triple law keeps the entire original joint law and has
the requested new marginal. No independence between `a` and `b` is needed.
Zero-mass old fibers contribute zero and require no conditional distribution.
The replacement depends on the old first coordinate through a kernel; a
division-free identity records the resulting conditional independence.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem exists_marginal_replacement_kernel {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} {q : α → ℝ} (hp : IsProbabilityWeight p)
    (hq : IsProbabilityWeight q) :
    ∃ ρ : (α × β) × α → ℝ, IsProbabilityWeight ρ ∧
      (∀ z, ∑ a', ρ (z, a') = p z) ∧ (∀ a', ∑ z, ρ (z, a') = q a') ∧
        (∑ z with z.1.1 ≠ z.2, ρ z) = weightDist (firstWeight p) q ∧
          ∀ a b a', firstWeight p a * ρ ((a, b), a') =
            p (a, b) * (∑ b', ρ ((a, b'), a')) := by
  have marginal_nonneg (a : α) : 0 ≤ firstWeight p a :=
    Finset.sum_nonneg fun b _ => hp.1 (a, b)
  have marginal : IsProbabilityWeight (firstWeight p) := by
    refine ⟨marginal_nonneg, ?_⟩
    simpa only [firstWeight, ← Fintype.sum_prod_type] using hp.2
  obtain ⟨r, hr, row, column, disagreement⟩ := exists_maximal_coupling marginal hq
  let ρ (z : (α × β) × α) := p z.1 * r (z.1.1, z.2) / firstWeight p z.1.1
  have nonnegative (z : (α × β) × α) : 0 ≤ ρ z :=
    div_nonneg (mul_nonneg (hp.1 z.1) (hr.1 (z.1.1, z.2))) (marginal_nonneg z.1.1)
  have preserve (z : α × β) : ∑ a', ρ (z, a') = p z := by
    simp only [ρ, ← Finset.sum_div, ← Finset.mul_sum, row]
    exact nonnegWeight_mul_mass_div (fun b => p (z.1, b)) (fun b => hp.1 (z.1, b)) z.2
  have collapse (a a' : α) : ∑ b, ρ ((a, b), a') = r (a, a') := by
    simp only [ρ, ← Finset.sum_div, ← Finset.sum_mul]
    change firstWeight p a * r (a, a') / firstWeight p a = r (a, a')
    rw [mul_comm, ← row a]
    exact nonnegWeight_mul_mass_div (fun a' => r (a, a')) (fun a' => hr.1 (a, a')) a'
  have replace (a' : α) : ∑ z, ρ (z, a') = q a' := by
    rw [Fintype.sum_prod_type]
    simp only [collapse, column]
  have total : ∑ z, ρ z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [preserve, hp.2]
  have kernel (a : α) (b : β) (a' : α) :
      firstWeight p a * ρ ((a, b), a') = p (a, b) * (∑ b', ρ ((a, b'), a')) := by
    rw [collapse]
    calc
      _ = (p (a, b) * firstWeight p a / firstWeight p a) * r (a, a') := by
        dsimp only [ρ]
        ring
      _ = _ := congrArg (fun c => c * r (a, a'))
        (nonnegWeight_mul_mass_div (fun b => p (a, b)) (fun b => hp.1 (a, b)) b)
  refine ⟨ρ, ⟨nonnegative, total⟩, preserve, replace, ?_, kernel⟩
  rw [← disagreement, Finset.sum_filter, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a' _
  by_cases same : a = a'
  · simp only [same, ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_const_zero]
  · simp only [same, ne_eq, not_false_eq_true, ↓reduceIte, collapse]

theorem exists_marginal_replacement_coupling {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} {q : α → ℝ} (hp : IsProbabilityWeight p)
    (hq : IsProbabilityWeight q) :
    ∃ ρ : (α × β) × α → ℝ, IsProbabilityWeight ρ ∧
      (∀ z, ∑ a', ρ (z, a') = p z) ∧ (∀ a', ∑ z, ρ (z, a') = q a') ∧
        (∑ z with z.1.1 ≠ z.2, ρ z) = weightDist (firstWeight p) q := by
  obtain ⟨ρ, hρ, preserve, replace, disagreement, _⟩ :=
    exists_marginal_replacement_kernel hp hq
  exact ⟨ρ, hρ, preserve, replace, disagreement⟩

end Algebraic.Cutwidth.Extractor.Internal
