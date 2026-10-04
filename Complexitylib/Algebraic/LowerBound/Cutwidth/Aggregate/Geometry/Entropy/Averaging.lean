/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Weighted
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Averaging designated pairs over coordinate subsets

Every fixed pair lies in the same number of subsets of a specified cardinality.
Double counting therefore supplies a partition retaining the exact expected number
of designated pairs, without probabilistic independence assumptions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

/-- An input subset retains at least the average number of designated distinct pairs. -/
theorem exists_subset_many_pairs {n a : Nat} (ha : 2 ≤ a) (han : a ≤ n)
    {J : Type*} [Fintype J] (left right : J → Fin n) (distinct : ∀ j, left j ≠ right j) :
    ∃ U : Finset (Fin n), U.card = a ∧
      (n.choose a) * (Finset.univ.filter fun j => left j ∈ U ∧ right j ∈ U).card ≥
        ((n - 2).choose (a - 2)) * Fintype.card J := by
  let sets := (Finset.univ : Finset (Fin n)).powersetCard a
  let score (U : Finset (Fin n)) :=
    (Finset.univ.filter fun j => left j ∈ U ∧ right j ∈ U).card
  have nonempty : sets.Nonempty := by
    apply Finset.card_pos.mp
    simpa [sets] using Nat.choose_pos han
  obtain ⟨U, hU, maximal⟩ := Finset.exists_max_image sets score nonempty
  refine ⟨U, (Finset.mem_powersetCard.mp hU).2, ?_⟩
  have each (j : J) : (sets.filter fun U => left j ∈ U ∧ right j ∈ U).card =
      (n - 2).choose (a - 2) := by
    have paircard : ({left j, right j} : Finset (Fin n)).card = 2 := by
      simp [distinct j]
    simpa only [sets, paircard, Finset.card_univ, Fintype.card_fin,
      Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      Finset.card_filter_powersetCard_subset {left j, right j} Finset.univ a
        (Finset.subset_univ _) (by rw [paircard]; exact ha)
  have total : ∑ U ∈ sets, score U =
      ((n - 2).choose (a - 2)) * Fintype.card J := by
    simp only [score, Finset.card_eq_sum_ones]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_boole, each]
    simp [Nat.mul_comm]
  have bound : ∑ V ∈ sets, score V ≤ sets.card * score U := by
    calc
      ∑ V ∈ sets, score V ≤ ∑ _V ∈ sets, score U :=
        Finset.sum_le_sum fun V hV => maximal V hV
      _ = sets.card * score U := by simp
  rw [total] at bound
  simpa only [sets, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, score] using bound

/-- The real-valued form of pair averaging has the exact two-coordinate survival factor. -/
theorem exists_subset_pair_ratio {n a : Nat} (ha : 2 ≤ a) (han : a ≤ n)
    {J : Type*} [Fintype J] (left right : J → Fin n) (distinct : ∀ j, left j ≠ right j) :
    ∃ U : Finset (Fin n), U.card = a ∧
      ((a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1))) * Fintype.card J ≤
        (Finset.univ.filter fun j => left j ∈ U ∧ right j ∈ U).card := by
  obtain ⟨U, hU, bound⟩ := exists_subset_many_pairs ha han left right distinct
  refine ⟨U, hU, ?_⟩
  have hn : (1 : ℝ) < n := by exact_mod_cast (by lia : 1 < n)
  have positive : (0 : ℝ) < n.choose a := by exact_mod_cast Nat.choose_pos han
  have identity : (n.choose a : ℝ) * ((a : ℝ) * (a - 1)) =
      ((n : ℝ) * (n - 1)) * ((n - 2).choose (a - 2) : ℝ) := by
    have h := Nat.choose_mul (n := n) ha
    have hR : (n.choose a : ℝ) * (a.choose 2 : ℝ) =
        (n.choose 2 : ℝ) * ((n - 2).choose (a - 2) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_choose_two, Nat.cast_choose_two] at hR
    linarith
  have boundR : ((n - 2).choose (a - 2) : ℝ) * Fintype.card J ≤
      (n.choose a : ℝ) *
        (Finset.univ.filter fun j => left j ∈ U ∧ right j ∈ U).card := by
    exact_mod_cast bound
  apply (mul_le_mul_iff_right₀ positive).mp
  have denom : (0 : ℝ) < n * (n - 1) := by positivity
  have rewrite_ratio : (n.choose a : ℝ) *
      (((a : ℝ) * (a - 1) / ((n : ℝ) * (n - 1))) * Fintype.card J) =
        ((n - 2).choose (a - 2) : ℝ) * Fintype.card J := by
    field_simp [(sub_pos.mpr hn).ne', (lt_trans zero_lt_one hn).ne']
    nlinarith [congrArg (fun z : ℝ => z * Fintype.card J) identity]
  rw [rewrite_ratio]
  exact boundR

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
