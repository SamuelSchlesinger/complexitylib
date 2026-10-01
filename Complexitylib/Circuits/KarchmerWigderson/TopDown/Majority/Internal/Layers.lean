/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Majority.Defs
public import Complexitylib.BooleanAnalysis.Fibers
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

/-!
# The two layers surrounding the majority threshold

The largest binomial coefficient is at least `2^n/(n+1)`, and its upper
neighbor is at least half as large. This gives a logarithmic entropy
deficit for both boundary layers, for even as well as odd input sizes.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

theorem le_majorityDeficitBound_internal (n : ℕ) : 128 ≤ majorityDeficitBound n := by
  have h := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    (show (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  unfold majorityDeficitBound
  linarith

theorem middle_choose_bound_internal (n : ℕ) : 2 ^ n ≤ (n + 1) * n.choose (n / 2) := by
  calc
    _ = ∑ r ∈ range (n + 1), n.choose r := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _r ∈ range (n + 1), n.choose (n / 2) :=
      sum_le_sum (fun r _ => Nat.choose_le_middle r n)
    _ = _ := by simp

theorem next_middle_choose_bound_internal {n : ℕ} (hn : 2 ≤ n) :
    n.choose (n / 2) ≤ 2 * n.choose (n / 2 + 1) := by
  have he := Nat.choose_succ_right_eq n (n / 2)
  have hh := Nat.mul_le_mul_left (n.choose (n / 2 + 1))
    (show n / 2 + 1 ≤ 2 * (n - n / 2) by omega)
  have hpos : 0 < n - n / 2 := by omega
  nlinarith

theorem weightLayer_deficit_internal {n r : ℕ} (hr : r ≤ n)
    (hcard : 2 ^ n ≤ (2 * (n + 1)) * n.choose r) :
    (weightLayer n r).Nonempty ∧ uniformDeficit (weightLayer n r) ≤ majorityDeficitBound n := by
  have hne : (weightLayer n r).Nonempty := by
    rw [← card_pos, weightLayer, card_filter_popCount_eq]
    exact Nat.choose_pos hr
  refine ⟨hne, ?_⟩
  have hd : uniformDeficit (weightLayer n r) ≤ Real.logb 2 (2 * ((n : ℝ) + 1)) := by
    apply (uniformDeficit_le_iff hne).mpr
    simp only [Fintype.card_fin, weightLayer, card_filter_popCount_eq]
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast,
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (by simpa only [mul_comm] using hcard : 2 ^ n ≤ n.choose r * (2 * (n + 1)))
  unfold majorityDeficitBound
  linarith

theorem majority_layers_deficit_internal {n : ℕ} (hn : 2 ≤ n) :
    ((weightLayer n (n / 2)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2)) ≤ majorityDeficitBound n) ∧
    ((weightLayer n (n / 2 + 1)).Nonempty ∧
      uniformDeficit (weightLayer n (n / 2 + 1)) ≤ majorityDeficitBound n) := by
  have hmid := middle_choose_bound_internal n
  have hnext := Nat.mul_le_mul_left (n + 1) (next_middle_choose_bound_internal hn)
  constructor
  · exact weightLayer_deficit_internal (by omega) (by nlinarith)
  · exact weightLayer_deficit_internal (by omega) (by nlinarith)

theorem popCount_update_true_internal {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hi : x i = false) :
    popCount (Function.update x i true) = popCount x + 1 := by
  have he : univ.filter (fun j => Function.update x i true j = true) =
      insert i (univ.filter (fun j => x j = true)) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [popCount, he, card_insert_of_notMem]
  · rfl
  · simp [hi]

theorem popCount_update_false_internal {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hi : x i = true) :
    popCount (Function.update x i false) + 1 = popCount x := by
  have he : univ.filter (fun j => Function.update x i false j = true) =
      (univ.filter (fun j => x j = true)).erase i := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [popCount, he]
  exact card_erase_add_one (by simp [hi])

end Complexity.BooleanAnalysis
