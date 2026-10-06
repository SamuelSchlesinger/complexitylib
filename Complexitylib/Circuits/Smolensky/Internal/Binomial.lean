/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# Binomial estimates for Smolensky's bound

The number of subsets of `Fin n` of size at most `n / 2 + t` is at most
`2^{n-1} + (t + 1) · C(n, ⌊n/2⌋)`, and `C(n, ⌊n/2⌋)² · (n + 1) ≤ 4^n`. Hence, when
`100 (t + 1)² ≤ n + 1`, at most `6/10` of all subsets have size at most
`n / 2 + t`.
-/


public section

namespace Complexity

namespace Smolensky

open Finset

/-- The central binomial coefficient satisfies `C(2m, m)² (2m + 1) ≤ 16^m`. -/
theorem centralBinom_sq_mul_le (m : ℕ) :
    m.centralBinom ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrec := Nat.succ_mul_centralBinom_succ m
    have key : (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1)) ≤
        (m + 1) ^ 2 * 16 ^ (m + 1) := by
      calc
        (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1)) =
            ((m + 1) * (m + 1).centralBinom) ^ 2 * (2 * m + 3) := by ring
        _ = (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (2 * m + 3) := by rw [hrec]
        _ = 4 * (2 * m + 1) * (2 * m + 3) * (m.centralBinom ^ 2 * (2 * m + 1)) := by
          ring
        _ ≤ 4 * (2 * m + 1) * (2 * m + 3) * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := by
          apply Nat.mul_le_mul_right
          ring_nf
          omega
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- The middle binomial coefficient satisfies `C(n, ⌊n/2⌋)² (n + 1) ≤ 4^n`. -/
theorem choose_half_sq_mul_le (n : ℕ) :
    n.choose (n / 2) ^ 2 * (n + 1) ≤ 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hhalf : 2 * m / 2 = m := by omega
    rw [hhalf, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    simpa using centralBinom_sq_mul_le m
  · have hhalf : (2 * m + 1) / 2 = m := by omega
    rw [hhalf]
    have hc : 2 * (2 * m + 1).choose m = (m + 1).centralBinom := by
      rw [Nat.centralBinom_eq_two_mul_choose,
        show 2 * (m + 1) = (2 * m + 1) + 1 by ring, Nat.choose_succ_succ',
        Nat.choose_symm_half]
      ring
    have hcentral := centralBinom_sq_mul_le (m + 1)
    rw [← hc] at hcentral
    have h16 : (16 : ℕ) ^ (m + 1) = 4 * 4 ^ (2 * m + 1) := by
      rw [pow_succ, pow_succ, pow_mul]
      norm_num
      ring
    rw [h16] at hcentral
    have hmain : 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1)) ≤ 4 * 4 ^ (2 * m + 1) :=
      calc
        4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1)) ≤
            (2 * (2 * m + 1).choose m) ^ 2 * (2 * (m + 1) + 1) := by
          ring_nf
          omega
        _ ≤ 4 * 4 ^ (2 * m + 1) := hcentral
    omega

/-- Complementation shows that at most half of all subsets have fewer than
`n / 2` elements. -/
theorem two_mul_card_small_le (n : ℕ) :
    2 * (univ.filter fun S : Finset (Fin n) => 2 * S.card < n).card ≤ 2 ^ n := by
  set A := univ.filter fun S : Finset (Fin n) => 2 * S.card < n
  set B := univ.filter fun S : Finset (Fin n) => n < 2 * S.card
  have hAB : A.card ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun S => Sᶜ) ?_ ?_
    · intro S hS
      simp only [A, B, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hS ⊢
      rw [Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_univ S
      simp only [Fintype.card_fin] at this
      omega
    · intro S _ T _ hST
      exact compl_injective hST
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro S _ hS
    omega
  have hunion : A.card + B.card ≤ 2 ^ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    calc
      (A ∪ B).card ≤ (univ : Finset (Finset (Fin n))).card := Finset.card_le_univ _
      _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  omega

/-- Subsets of size between `n / 2` and `n / 2 + t` number at most
`(t + 1) · C(n, ⌊n/2⌋)`. -/
theorem card_middle_le (n t : ℕ) :
    (univ.filter fun S : Finset (Fin n) =>
      n ≤ 2 * S.card ∧ S.card ≤ n / 2 + t).card ≤ (t + 1) * n.choose (n / 2) := by
  classical
  have hmaps : ∀ S ∈ (univ.filter fun S : Finset (Fin n) =>
      n ≤ 2 * S.card ∧ S.card ≤ n / 2 + t), S.card ∈ Finset.Icc ((n + 1) / 2) (n / 2 + t) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [Finset.mem_Icc]
    omega
  have hfiber : ∀ b ∈ Finset.Icc ((n + 1) / 2) (n / 2 + t),
      ((univ.filter fun S : Finset (Fin n) =>
        n ≤ 2 * S.card ∧ S.card ≤ n / 2 + t).filter fun S => S.card = b).card ≤
          n.choose (n / 2) := by
    intro b _
    calc
      _ ≤ (Finset.powersetCard b (univ : Finset (Fin n))).card := by
        apply Finset.card_le_card
        intro S hS
        simp only [Finset.mem_filter] at hS
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS.2⟩
      _ = n.choose b := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ ≤ n.choose (n / 2) := Nat.choose_le_middle b n
  calc
    _ ≤ n.choose (n / 2) * (Finset.Icc ((n + 1) / 2) (n / 2 + t)).card :=
      Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber
    _ ≤ n.choose (n / 2) * (t + 1) := by
      apply Nat.mul_le_mul_left
      rw [Nat.card_Icc]
      omega
    _ = (t + 1) * n.choose (n / 2) := Nat.mul_comm _ _

/-- When `100 (t + 1)² ≤ n + 1`, at most `6/10` of the subsets of `Fin n` have
at most `n / 2 + t` elements. -/
theorem ten_mul_card_le_internal (n t : ℕ) (h : 100 * (t + 1) ^ 2 ≤ n + 1) :
    10 * (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + t).card ≤ 6 * 2 ^ n := by
  set A := univ.filter fun S : Finset (Fin n) => 2 * S.card < n
  set M := univ.filter fun S : Finset (Fin n) => n ≤ 2 * S.card ∧ S.card ≤ n / 2 + t
  have hsub : (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + t) ⊆ A ∪ M := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [A, M, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hA : 2 * A.card ≤ 2 ^ n := two_mul_card_small_le n
  have hM : M.card ≤ (t + 1) * n.choose (n / 2) := card_middle_le n t
  have hC := choose_half_sq_mul_le n
  have hmid : 10 * ((t + 1) * n.choose (n / 2)) ≤ 2 ^ n := by
    have hsq : (10 * ((t + 1) * n.choose (n / 2))) ^ 2 ≤ (2 ^ n) ^ 2 := by
      calc
        (10 * ((t + 1) * n.choose (n / 2))) ^ 2 =
            (100 * (t + 1) ^ 2) * n.choose (n / 2) ^ 2 := by ring
        _ ≤ (n + 1) * n.choose (n / 2) ^ 2 := Nat.mul_le_mul_right _ h
        _ = n.choose (n / 2) ^ 2 * (n + 1) := Nat.mul_comm _ _
        _ ≤ 4 ^ n := hC
        _ = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  calc
    10 * (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + t).card ≤
        10 * (A.card + M.card) :=
      Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    _ ≤ 6 * 2 ^ n := by
      have : 10 * M.card ≤ 10 * ((t + 1) * n.choose (n / 2)) := Nat.mul_le_mul_left _ hM
      omega

end Smolensky

end Complexity
