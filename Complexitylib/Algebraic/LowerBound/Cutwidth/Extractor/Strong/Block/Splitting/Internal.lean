/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rowwise finite entropy repair

A uniform replacement preserves a row's total mass. Large rows satisfy the
conditional cap by the original point bound, and small rows satisfy it by
the second alphabet's cardinality. The variation distance is bounded by
the total mass in replaced rows. Row averaging also preserves every original
joint point-mass cap, independently of normalization or nonnegativity.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem twoBlockRepair_nonnegative {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (nonnegative : ∀ x, 0 ≤ p x) (K : Nat) (μ : ℝ) :
    ∀ x, 0 ≤ twoBlockRepair p K μ x := by
  intro x
  unfold twoBlockRepair
  split
  · exact div_nonneg (Finset.sum_nonneg fun b _ => nonnegative (x.1, b))
      (Nat.cast_nonneg _)
  · exact nonnegative x

theorem twoBlockRepair_capped {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (N K : Nat) (μ : ℝ) (cap : CappedWeight p N) :
    CappedWeight (twoBlockRepair p K μ) N := by
  intro ab
  let : Nonempty β := ⟨ab.2⟩
  have card_pos : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  unfold twoBlockRepair
  split
  · have row_cap : (N : ℝ) * firstWeight p ab.1 ≤ Fintype.card β := by
      unfold firstWeight
      rw [Finset.mul_sum]
      calc
        ∑ b, (N : ℝ) * p (ab.1, b) ≤ ∑ _b : β, (1 : ℝ) :=
          Finset.sum_le_sum fun b _ => cap (ab.1, b)
        _ = Fintype.card β := by simp
    rw [← mul_div_assoc]
    exact (div_le_iff₀ card_pos).mpr (by simpa using row_cap)
  · exact cap ab

theorem twoBlockRepair_firstWeight {α β : Type*} [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (K : Nat) (μ : ℝ) :
    firstWeight (twoBlockRepair p K μ) = firstWeight p := by
  funext a
  change (∑ b, twoBlockRepair p K μ (a, b)) = firstWeight p a
  by_cases low : firstWeight p a < (K : ℝ) * μ
  · simp only [twoBlockRepair, low, ite_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
  · simp only [twoBlockRepair, low, ite_false]
    rfl

theorem twoBlockRepair_probability {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) (K : Nat) (μ : ℝ) :
    IsProbabilityWeight (twoBlockRepair p K μ) := by
  refine ⟨twoBlockRepair_nonnegative p probability.1 K μ, ?_⟩
  rw [Fintype.sum_prod_type]
  change (∑ a, firstWeight (twoBlockRepair p K μ) a) = 1
  rw [twoBlockRepair_firstWeight]
  simpa only [firstWeight, Fintype.sum_prod_type] using probability.2

theorem twoBlockRepair_conditional_cap {α β : Type*} [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (nonnegative : ∀ x, 0 ≤ p x) {K : Nat} {μ : ℝ}
    (size : K ≤ Fintype.card β) (cap : ∀ x, p x ≤ μ) :
    ∀ a b, (K : ℝ) * twoBlockRepair p K μ (a, b) ≤
      firstWeight (twoBlockRepair p K μ) a := by
  intro a b
  rw [twoBlockRepair_firstWeight]
  have row_nonnegative : 0 ≤ firstWeight p a :=
    Finset.sum_nonneg fun b _ => nonnegative (a, b)
  by_cases low : firstWeight p a < (K : ℝ) * μ
  · rw [twoBlockRepair, ite_eq_left low]
    calc
      _ ≤ (Fintype.card β : ℝ) * (firstWeight p a / Fintype.card β) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast size)
          (div_nonneg row_nonnegative (Nat.cast_nonneg _))
      _ = firstWeight p a := by field_simp
  · rw [twoBlockRepair, ite_eq_right low]
    exact (mul_le_mul_of_nonneg_left (cap (a, b)) (Nat.cast_nonneg K)).trans
      (le_of_not_gt low)

theorem twoBlockRepair_row_l1_le {α β : Type*} [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (nonnegative : ∀ x, 0 ≤ p x) (K : Nat) (μ : ℝ) (a : α) :
    (∑ b, |p (a, b) - twoBlockRepair p K μ (a, b)|) ≤
      2 * (if firstWeight p a < (K : ℝ) * μ then firstWeight p a else 0) := by
  by_cases low : firstWeight p a < (K : ℝ) * μ
  · rw [ite_eq_left low]
    calc
      _ ≤ ∑ b, (p (a, b) + twoBlockRepair p K μ (a, b)) := by
        apply Finset.sum_le_sum
        intro b _
        have triangle := abs_sub_le (p (a, b)) 0 (twoBlockRepair p K μ (a, b))
        simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (nonnegative (a, b)),
          abs_of_nonneg (twoBlockRepair_nonnegative p nonnegative K μ (a, b))] using triangle
      _ = firstWeight p a + firstWeight (twoBlockRepair p K μ) a := by
        rw [Finset.sum_add_distrib]
        rfl
      _ = 2 * firstWeight p a := by rw [twoBlockRepair_firstWeight]; ring
  · simp only [twoBlockRepair, low, ite_false, sub_self, abs_zero,
      Finset.sum_const_zero, mul_zero, le_refl]

theorem twoBlockRepair_dist_le_low_mass {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (nonnegative : ∀ x, 0 ≤ p x) (K : Nat) (μ : ℝ) :
    weightDist p (twoBlockRepair p K μ) ≤
      ∑ a, if firstWeight p a < (K : ℝ) * μ then firstWeight p a else 0 := by
  unfold weightDist
  rw [Fintype.sum_prod_type]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ ∑ a, 2 * (if firstWeight p a < (K : ℝ) * μ then firstWeight p a else 0) :=
      Finset.sum_le_sum fun a _ => twoBlockRepair_row_l1_le p nonnegative K μ a
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

theorem twoBlockRepair_dist_le {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) {K : Nat} {μ : ℝ}
    (cap : ∀ x, p x ≤ μ) :
    weightDist p (twoBlockRepair p K μ) ≤ (Fintype.card α : ℝ) * K * μ := by
  have cap_nonnegative : 0 ≤ μ := by
    by_contra negative
    have total : (∑ x, p x) ≤ 0 :=
      Finset.sum_nonpos fun x _ => (cap x).trans (le_of_lt (lt_of_not_ge negative))
    rw [probability.2] at total
    norm_num at total
  calc
    _ ≤ ∑ a, if firstWeight p a < (K : ℝ) * μ then firstWeight p a else 0 :=
      twoBlockRepair_dist_le_low_mass p probability.1 K μ
    _ ≤ ∑ _ : α, (K : ℝ) * μ := by
      apply Finset.sum_le_sum
      intro a _
      split
      · exact le_of_lt ‹_›
      · exact mul_nonneg (Nat.cast_nonneg _) cap_nonnegative
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem twoBlockRepair_first_cap {α β : Type*} [Fintype β] [Nonempty β]
    (p : α × β → ℝ) {K : Nat} {μ : ℝ} (cap : ∀ x, p x ≤ μ)
    (budget : (K : ℝ) * Fintype.card β * μ ≤ 1) :
    CappedWeight (firstWeight (twoBlockRepair p K μ)) K := by
  intro a
  rw [twoBlockRepair_firstWeight]
  have row_cap : firstWeight p a ≤ (Fintype.card β : ℝ) * μ := by
    calc
      _ ≤ ∑ _ : β, μ := Finset.sum_le_sum fun b _ => cap (a, b)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_left row_cap (Nat.cast_nonneg K)).trans
    (by simpa only [mul_assoc] using budget)

theorem exists_twoBlock_repair {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) {K : Nat} {μ : ℝ}
    (positive : 0 < K) (size : K ≤ Fintype.card β) (cap : ∀ x, p x ≤ μ)
    (budget : (K : ℝ) * Fintype.card β * μ ≤ 1) :
    ∃ q : α × β → ℝ, IsProbabilityWeight q ∧ firstWeight q = firstWeight p ∧
      CappedWeight (firstWeight q) K ∧
      (∀ a b, (K : ℝ) * q (a, b) ≤ firstWeight q a) ∧
      weightDist p q ≤ (Fintype.card α : ℝ) * K * μ := by
  let : Nonempty β := Fintype.card_pos_iff.mp (positive.trans_le size)
  exact ⟨twoBlockRepair p K μ, twoBlockRepair_probability p probability K μ,
    twoBlockRepair_firstWeight p K μ, twoBlockRepair_first_cap p cap budget,
    twoBlockRepair_conditional_cap p probability.1 size cap,
    twoBlockRepair_dist_le p probability cap⟩

theorem twoBlock_pow_two_budget {m t k e : Nat} (entropy : m + t + e ≤ k) :
    (2 : ℝ) ^ m * 2 ^ t * (2 ^ k)⁻¹ ≤ (2 ^ e)⁻¹ := by
  have powers : (2 : ℝ) ^ (m + t + e) ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) entropy
  rw [pow_add, pow_add] at powers
  rw [← one_div (2 ^ e : ℝ)]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = ((2 : ℝ) ^ m * 2 ^ t * 2 ^ e) / 2 ^ k := by ring
    _ ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by simpa using powers)

private theorem twoBlock_pow_two_point_cap {α : Type*} (p : α → ℝ) {k : Nat}
    (cap : CappedWeight p (2 ^ k)) : ∀ x, p x ≤ ((2 : ℝ) ^ k)⁻¹ := by
  intro x
  have point := cap x
  have casting : ((2 ^ k : Nat) : ℝ) = (2 : ℝ) ^ k := by norm_cast
  rw [casting] at point
  rw [← one_div ((2 : ℝ) ^ k)]
  exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using point)

theorem exists_twoBlock_repair_pow_two {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (probability : IsProbabilityWeight p) {m t k e : Nat}
    (card_first : Fintype.card α = 2 ^ m) (card_second : Fintype.card β = 2 ^ m)
    (cap : CappedWeight p (2 ^ k)) (width : t ≤ m) (entropy : m + t + e ≤ k) :
    ∃ q : α × β → ℝ, IsProbabilityWeight q ∧ firstWeight q = firstWeight p ∧
      CappedWeight (firstWeight q) (2 ^ t) ∧
      (∀ a b, ((2 ^ t : Nat) : ℝ) * q (a, b) ≤ firstWeight q a) ∧
      weightDist p q ≤ ((2 : ℝ) ^ e)⁻¹ := by
  have point_cap := twoBlock_pow_two_point_cap p cap
  have cost := twoBlock_pow_two_budget entropy
  have error_le_one : ((2 : ℝ) ^ e)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have budget : ((2 ^ t : Nat) : ℝ) * Fintype.card β * ((2 : ℝ) ^ k)⁻¹ ≤ 1 := by
    rw [card_second]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    simpa only [mul_comm (2 ^ t : ℝ) (2 ^ m)] using cost.trans error_le_one
  obtain ⟨q, hq, marginal, first_cap, conditional, distance⟩ :=
    exists_twoBlock_repair p probability (by positivity : 0 < 2 ^ t)
      (by rw [card_second]; exact Nat.pow_le_pow_right (by norm_num) width) point_cap budget
  refine ⟨q, hq, marginal, first_cap, conditional, distance.trans ?_⟩
  rw [card_first]
  exact_mod_cast cost

theorem exists_twoBlock_repair_pow_two_capped {α : Type*} [Fintype α]
    (p : α × α → ℝ) (probability : IsProbabilityWeight p) {m s k e : Nat}
    (card : Fintype.card α = 2 ^ m) (cap : CappedWeight p (2 ^ k))
    (width : s ≤ m) (entropy : m + s + e ≤ k) :
    ∃ q : α × α → ℝ, IsProbabilityWeight q ∧ CappedWeight q (2 ^ k) ∧
      IsBlockSource (fun x : Fin 2 → α => q (x 0, x 1)) (2 ^ s) ∧
      firstWeight q = firstWeight p ∧ weightDist p q ≤ ((2 : ℝ) ^ e)⁻¹ := by
  let : Nonempty α := Fintype.card_pos_iff.mp (by rw [card]; positivity)
  have point_cap := twoBlock_pow_two_point_cap p cap
  have cost := twoBlock_pow_two_budget entropy
  have error_le_one : ((2 : ℝ) ^ e)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have budget : ((2 ^ s : Nat) : ℝ) * Fintype.card α * ((2 : ℝ) ^ k)⁻¹ ≤ 1 := by
    rw [card]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    simpa only [mul_comm (2 ^ s : ℝ) (2 ^ m)] using cost.trans error_le_one
  let q := twoBlockRepair p (2 ^ s) (((2 : ℝ) ^ k)⁻¹)
  have hq : IsProbabilityWeight q := twoBlockRepair_probability p probability _ _
  refine ⟨q, hq, twoBlockRepair_capped p (2 ^ k) (2 ^ s) _ cap, ?_,
    twoBlockRepair_firstWeight p _ _, ?_⟩
  · apply (isBlockSource_two_iff q (2 ^ s)).mpr
    refine ⟨hq, twoBlockRepair_first_cap p point_cap budget, ?_⟩
    exact twoBlockRepair_conditional_cap p probability.1
      (by rw [card]; exact Nat.pow_le_pow_right (by norm_num) width) point_cap
  · refine (twoBlockRepair_dist_le p probability point_cap).trans ?_
    rw [card]
    exact_mod_cast cost

end Algebraic.Cutwidth.Extractor.Internal
