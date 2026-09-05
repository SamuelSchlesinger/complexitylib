/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# A second-moment support bound

The Paley–Zygmund style inequality behind Dinur's powering estimate: a
nonnegative random variable is nonzero on a set at least as large as the square
of its mean over its second moment. Written with sums rather than expectations,
so that the normalising cardinality cancels on its own:

`(∑ N) ^ 2 ≤ |support N| · ∑ N ^ 2`

In the powering analysis `N` counts how many *faulty* edges a random walk
traverses. The first moment is proportional to the gap, the second moment is
controlled by the expander mixing lemma, and this inequality converts the two
into a lower bound on the probability that the walk meets a faulty edge at all
— which is what the powered constraint detects.

## Main results

- `sq_sum_le_card_support_mul_sum_sq` — the inequality above
- `sq_sum_div_sum_sq_le_card_support` — its ratio form
- `card_ge_of_moments` — Paley–Zygmund in counting form
-/

@[expose] public section

namespace Complexity

open Classical in
/-- **Second-moment support bound.** The square of a sum is at most the size of
the summand's support times the sum of squares. -/
theorem sq_sum_le_card_support_mul_sum_sq {ι : Type*} [Fintype ι] (N : ι → ℝ) :
    (∑ i, N i) ^ 2 ≤ ((Finset.univ.filter fun i => N i ≠ 0).card : ℝ) * ∑ i, (N i) ^ 2 := by
  classical
  have hcross : ∑ i, (if N i ≠ 0 then (1 : ℝ) else 0) * N i = ∑ i, N i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : N i = 0 <;> simp [h]
  have hfsq : ∑ i, (if N i ≠ 0 then (1 : ℝ) else 0) ^ 2
      = ((Finset.univ.filter fun i => N i ≠ 0).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : N i = 0 <;> simp [h]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => if N i ≠ 0 then (1 : ℝ) else 0) N
  rwa [hcross, hfsq] at hcs

open Classical in
/-- The ratio form: the support is at least the mean-square ratio. -/
theorem sq_sum_div_sum_sq_le_card_support {ι : Type*} [Fintype ι] (N : ι → ℝ)
    (h : 0 < ∑ i, (N i) ^ 2) :
    (∑ i, N i) ^ 2 / (∑ i, (N i) ^ 2)
      ≤ ((Finset.univ.filter fun i => N i ≠ 0).card : ℝ) := by
  rw [div_le_iff₀ h]
  exact sq_sum_le_card_support_mul_sum_sq N

open Classical in
/-- **Paley–Zygmund, in counting form.** If a nonnegative count has first moment
at least `A` and second moment at most `B`, then at least `A ^ 2 / B` of the
indices carry a nonzero count. Any `S` containing the support inherits the
bound — in the powering argument `S` is the set of unsatisfied constraints and
the count is the number of crossings that break one. -/
theorem card_ge_of_moments {ι : Type*} [Fintype ι] (N : ι → ℝ) (S : Finset ι)
    (hsupp : ∀ i, N i ≠ 0 → i ∈ S) {A B : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ ∑ i, N i)
    (hB : ∑ i, (N i) ^ 2 ≤ B) (hB0 : 0 < B) :
    A ^ 2 / B ≤ (S.card : ℝ) := by
  classical
  have h1 := sq_sum_le_card_support_mul_sum_sq N
  have h2 : ((Finset.univ.filter fun i => N i ≠ 0).card : ℝ) ≤ (S.card : ℝ) := by
    have hsub : (Finset.univ.filter fun i => N i ≠ 0) ⊆ S := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hsupp i hi
    exact_mod_cast Finset.card_le_card hsub
  have h3 : A ^ 2 ≤ (∑ i, N i) ^ 2 := by nlinarith [hA, hA0]
  have h4 : (0 : ℝ) ≤ ∑ i, (N i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h5 : A ^ 2 ≤ (S.card : ℝ) * B := by
    calc A ^ 2 ≤ (∑ i, N i) ^ 2 := h3
      _ ≤ ((Finset.univ.filter fun i => N i ≠ 0).card : ℝ) * ∑ i, (N i) ^ 2 := h1
      _ ≤ (S.card : ℝ) * B := by
          refine mul_le_mul h2 hB h4 ?_
          positivity
  rw [div_le_iff₀ hB0]
  exact h5

end Complexity
