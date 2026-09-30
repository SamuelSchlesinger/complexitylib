/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite covering by a dense relation

The elementary greedy covering argument used in sparse synthesis: if each
target is covered by at least a fixed fraction of the candidates, successive
choices shrink the uncovered set geometrically.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open scoped BigOperators

variable {α β : Type} [Fintype α]

theorem sum_card_filter_comm (s : Finset β) (r : α → β → Prop) [DecidableRel r] :
    ∑ a : α, (s.filter (r a)).card =
      ∑ b ∈ s, (Finset.univ.filter fun a => r a b).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem exists_dense_row (s : Finset β) (r : α → β → Prop) [DecidableRel r]
    [Nonempty α]
    (a : ℕ) (dense : ∀ b ∈ s, Fintype.card α ≤
      a * (Finset.univ.filter fun x => r x b).card) :
    ∃ x, s.card ≤ a * (s.filter (r x)).card := by
  by_contra missing
  push Not at missing
  have upper : ∑ x : α, a * (s.filter (r x)).card < Fintype.card α * s.card := by
    simpa [Nat.mul_comm] using Finset.sum_lt_sum_of_nonempty
      (s := Finset.univ) Finset.univ_nonempty (fun x _ => missing x)
  have lower := Finset.sum_le_sum dense
  rw [← Finset.mul_sum, sum_card_filter_comm] at upper
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at lower
  nlinarith

theorem exists_partial_cover (s : Finset β) (r : α → β → Prop) [DecidableRel r]
    [Nonempty α] [DecidableEq α]
    (a : ℕ) (positive : 0 < a)
    (dense : ∀ b ∈ s, Fintype.card α ≤
      a * (Finset.univ.filter fun x => r x b).card) (steps : ℕ) :
    ∃ chosen : Finset α, chosen.card ≤ steps ∧
      ((s.filter fun b => ∀ x ∈ chosen, ¬ r x b).card : ℝ) ≤
        s.card * (1 - 1 / (a : ℝ)) ^ steps := by
  have apos : (0 : ℝ) < a := by exact_mod_cast positive
  have ratio : 0 ≤ 1 - 1 / (a : ℝ) := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast positive
    exact sub_nonneg.mpr ((div_le_one apos).mpr this)
  induction steps generalizing s with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ steps ih =>
    obtain ⟨x, hx⟩ := exists_dense_row s r a dense
    let rest := s.filter fun b => ¬ r x b
    have restBound : (rest.card : ℝ) ≤ s.card * (1 - 1 / (a : ℝ)) := by
      have split := Finset.card_filter_add_card_filter_not (s := s) (p := r x)
      have split' : ((s.filter (r x)).card : ℝ) + rest.card = s.card := by
        exact_mod_cast split
      have hx' : (s.card : ℝ) ≤ (a : ℝ) * (s.filter (r x)).card := by exact_mod_cast hx
      have equal : (s.card : ℝ) * (1 - 1 / (a : ℝ)) =
          ((s.card : ℝ) * a - s.card) / a := by field_simp
      rw [equal]
      apply (le_div_iff₀ apos).mpr
      nlinarith
    obtain ⟨chosen, hcard, hremain⟩ := ih rest
      (fun b hb => dense b (Finset.mem_filter.mp hb).1)
    refine ⟨insert x chosen, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
    have equal : s.filter (fun b => ∀ y ∈ insert x chosen, ¬ r y b) =
        rest.filter (fun b => ∀ y ∈ chosen, ¬ r y b) := by
      ext b
      simp [rest, and_assoc]
    rw [equal]
    calc
      _ ≤ (rest.card : ℝ) * (1 - 1 / (a : ℝ)) ^ steps := hremain
      _ ≤ ((s.card : ℝ) * (1 - 1 / (a : ℝ))) *
          (1 - 1 / (a : ℝ)) ^ steps :=
        mul_le_mul_of_nonneg_right restBound (pow_nonneg ratio _)
      _ = _ := by rw [pow_succ]; ring

theorem exists_cover (s : Finset β) (r : α → β → Prop) [DecidableRel r]
    [Nonempty α] [DecidableEq α] (a length : ℕ) (positive : 0 < a)
    (size : s.card ≤ 4 ^ length)
    (dense : ∀ b ∈ s, Fintype.card α ≤
      a * (Finset.univ.filter fun x => r x b).card) :
    ∃ chosen : Finset α, chosen.card ≤ (4 * length + 1) * a ∧
      ∀ b ∈ s, ∃ x ∈ chosen, r x b := by
  obtain ⟨chosen, hcard, hremain⟩ :=
    exists_partial_cover s r a positive dense ((4 * length + 1) * a)
  have apos : (0 : ℝ) < a := by exact_mod_cast positive
  have ratio : 0 ≤ 1 - 1 / (a : ℝ) := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast positive
    exact sub_nonneg.mpr ((div_le_one apos).mpr this)
  have decay : (1 - 1 / (a : ℝ)) ^ ((4 * length + 1) * a) ≤
      Real.exp (-(4 * (length : ℝ) + 1)) := by
    have expBound : 1 - 1 / (a : ℝ) ≤ Real.exp (-1 / (a : ℝ)) := by
      simpa only [neg_div, sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(1 / (a : ℝ)))
    calc
      _ ≤ (Real.exp (-1 / (a : ℝ))) ^ ((4 * length + 1) * a) :=
        pow_le_pow_left₀ ratio expBound _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
  have growth : (4 : ℝ) ^ length ≤ Real.exp (4 * (length : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by norm_num)
    linarith [Real.add_one_le_exp (4 : ℝ)]
  have small : (4 : ℝ) ^ length * Real.exp (-(4 * (length : ℝ) + 1)) < 1 := by
    calc
      _ ≤ Real.exp (4 * (length : ℝ)) * Real.exp (-(4 * (length : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right growth (Real.exp_nonneg _)
      _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring
      _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have last : ((s.filter fun b => ∀ x ∈ chosen, ¬ r x b).card : ℝ) < 1 := by
    apply lt_of_le_of_lt hremain
    apply lt_of_le_of_lt _ small
    exact mul_le_mul (by exact_mod_cast size) decay (pow_nonneg ratio _)
      (by positivity)
  have empty : (s.filter fun b => ∀ x ∈ chosen, ¬ r x b).card = 0 := by
    have : (s.filter fun b => ∀ x ∈ chosen, ¬ r x b).card < 1 := by exact_mod_cast last
    omega
  refine ⟨chosen, hcard, fun b hb => ?_⟩
  by_contra absent
  push Not at absent
  have member : b ∈ s.filter (fun b => ∀ x ∈ chosen, ¬ r x b) :=
    Finset.mem_filter.mpr ⟨hb, absent⟩
  have positive := Finset.card_pos.mpr ⟨b, member⟩
  omega

end Complexity.CircuitSparseSynthesis.Internal
