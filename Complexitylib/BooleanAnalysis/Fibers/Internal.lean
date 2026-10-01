/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Fibers.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional-fiber entropy estimates

A finite log-sum inequality proves Korten's entropy lemma (Lemma 4).
A bijection with the full-cube fiber verifies the dimension convention.
Markov's inequality gives the `63/64` good-fiber estimate needed in the
improved mirror-set argument.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

theorem mul_log_tangent_internal {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    a * Real.log c + a - c ≤ a * Real.log a := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, zero_add, zero_sub]
    linarith
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hc ha)) ha.le
  rw [Real.log_div hc.ne' ha.ne'] at h
  have he : a * (c / a) = c := by field_simp
  nlinarith

theorem sum_mul_log_ge_internal {β : Type*} [Fintype β] [Nonempty β]
    {m : β → ℝ} (hm : ∀ b, 0 ≤ m b) (hpos : 0 < ∑ b, m b) :
    (∑ b, m b) * Real.log ((∑ b, m b) / Fintype.card β) ≤
      ∑ b, m b * Real.log (m b) := by
  let c := (∑ b, m b) / Fintype.card β
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hc : 0 < c := div_pos hpos hB
  have h := sum_le_sum (s := univ) (fun b _ => mul_log_tangent_internal (hm b) hc)
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_mul, sum_const, card_univ,
    nsmul_eq_mul] at h
  have he : (Fintype.card β : ℝ) * c = ∑ b, m b := by dsimp [c]; field_simp
  rw [he] at h
  simpa only [add_sub_cancel_right] using h

theorem expect_log_card_fiber_internal {α β : Type*} [Fintype β] [Nonempty β]
    (X : Finset α) (hX : X.Nonempty) (g : α → β) :
    Real.log X.card - Real.log (Fintype.card β) ≤
      𝔼 x ∈ X, Real.log (X.filter (fun y => g y = g x)).card := by
  let m : β → ℝ := fun b => (X.filter fun x => g x = b).card
  have hsum : (∑ b, m b) = (X.card : ℝ) := by
    dsimp [m]
    exact_mod_cast (card_eq_sum_card_fiberwise (s := X) (t := univ)
      (f := g) (by intro x hx; exact mem_univ _) ).symm
  have hN : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hX
  have hB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have h := sum_mul_log_ge_internal (m := m) (by intro b; dsimp [m]; positivity) (by simpa [hsum])
  rw [hsum, Real.log_div hN.ne' hB.ne'] at h
  have he : (∑ x ∈ X, Real.log (X.filter (fun y => g y = g x)).card) =
      ∑ b, m b * Real.log (m b) := by
    rw [← sum_fiberwise' X g (fun b => Real.log (m b))]
    simp only [sum_const, nsmul_eq_mul]
    rfl
  rw [expect_eq_sum_div_card, he]
  exact (le_div_iff₀ hN).mpr (by nlinarith)

theorem card_coordinateFiber_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (s x : ι → Bool) :
    (coordinateFiber X s x).card =
      (X.filter fun y => (fun i : {i // s i ≠ true} => y i) =
        (fun i : {i // s i ≠ true} => x i)).card := by
  refine card_bij (fun z _ => completePattern s x z) ?_ ?_ ?_
  · intro z hz
    refine mem_filter.mpr ⟨(mem_filter.mp hz).2, ?_⟩
    funext i
    simp [completePattern, i.property]
  · intro z hz w hw he
    funext i
    have h := congrFun he i
    simpa [completePattern, i.property] using h
  · intro y hy
    have he : completePattern s x (fun i => y i) = y := by
      funext i
      by_cases hi : s i = true
      · simp [completePattern, hi]
      · have h := congrFun (mem_filter.mp hy).2 ⟨i, hi⟩
        simpa [completePattern, hi] using h.symm
    refine ⟨fun i => y i, ?_, he⟩
    exact mem_filter.mpr ⟨mem_univ _, by rw [he]; exact (mem_filter.mp hy).1⟩

theorem coordinateFiber_nonempty_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Finset (ι → Bool)} (s : ι → Bool) {x : ι → Bool} (hx : x ∈ X) :
    (coordinateFiber X s x).Nonempty := by
  refine ⟨fun i => x i, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  have he : completePattern s x (fun i => x i) = x := by
    funext i
    simp [completePattern]
  rwa [he]

theorem uniformDeficit_nonneg_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) : 0 ≤ uniformDeficit X := by
  by_cases hx : X.Nonempty
  · have hpos : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hx
    have hc : (X.card : ℝ) ≤ (2 : ℝ) ^ (Fintype.card ι : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast (show X.card ≤ 2 ^ Fintype.card ι by simpa using card_le_univ X)
    have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos).mpr hc
    exact sub_nonneg.mpr h
  · rw [not_nonempty_iff_eq_empty.mp hx]
    simp [uniformDeficit]

theorem expect_uniformDeficit_coordinateFiber_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool) :
    (𝔼 x ∈ X, uniformDeficit (coordinateFiber X s x)) ≤ uniformDeficit X := by
  have h := expect_log_card_fiber_internal X hX (fun x (i : {i // s i ≠ true}) => x i)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (Fintype.card {i // s i = true} : ℝ) +
      Fintype.card {i // s i ≠ true} = Fintype.card ι := by
    have hle := Fintype.card_subtype_le (fun i => s i = true)
    have he : Fintype.card {i // s i = true} +
        Fintype.card {i // s i ≠ true} = Fintype.card ι := by
      rw [Fintype.card_subtype_compl]
      omega
    exact_mod_cast he
  have he : (𝔼 x ∈ X, uniformDeficit (coordinateFiber X s x)) =
      Fintype.card {i // s i = true} -
        (𝔼 x ∈ X, Real.log (X.filter fun y =>
          (fun i : {i // s i ≠ true} => y i) =
          (fun i : {i // s i ≠ true} => x i)).card) / Real.log 2 := by
    simp only [uniformDeficit, Real.logb, expect_sub_distrib, ← expect_div,
      expect_const hX, card_coordinateFiber_internal]
  rw [he]
  have hcard : Real.log (Fintype.card ({i // s i ≠ true} → Bool)) =
      Fintype.card {i // s i ≠ true} * Real.log 2 := by
    simp
  rw [hcard] at h
  dsimp [uniformDeficit, Real.logb]
  have hd := div_le_div_of_nonneg_right h hl.le
  simp only [sub_div, mul_div_cancel_right₀ _ hl.ne', ne_eq] at hd
  linarith only [hc, hd]

theorem coordinateFiber_good_probability_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (s : ι → Bool)
    {k : ℝ} (hk : 0 < k) (hdef : uniformDeficit X ≤ k) :
    63 / 64 ≤ 𝔼 x ∈ X, if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then
      (1 : ℝ) else 0 := by
  have hp : 0 < 64 * k := by positivity
  have hpoint (x : ι → Bool) :
      1 ≤ (if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then (1 : ℝ) else 0) +
        uniformDeficit (coordinateFiber X s x) / (64 * k) := by
    by_cases hx : uniformDeficit (coordinateFiber X s x) ≤ 64 * k
    · rw [ite_eq_left hx]
      have := div_nonneg (uniformDeficit_nonneg_internal (coordinateFiber X s x)) hp.le
      linarith
    · rw [ite_eq_right hx, zero_add]
      exact (le_div_iff₀ hp).mpr (by linarith)
  have h := expect_le_expect (s := X) (fun x _ => hpoint x)
  rw [expect_const hX, expect_add_distrib, ← expect_div] at h
  have hd := div_le_div_of_nonneg_right
    ((expect_uniformDeficit_coordinateFiber_internal X hX s).trans hdef) hp.le
  have he : k / (64 * k) = 1 / 64 := by field_simp
  rw [he] at hd
  linarith

theorem sum_uniformMass_internal {α : Type*} [Fintype α] [DecidableEq α]
    {X : Finset α} (hX : X.Nonempty) : (∑ x, uniformMass X x) = 1 := by
  have hp : (X.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hX).ne'
  simp [uniformMass, hp]

theorem sum_uniformMass_mul_internal {α : Type*} [Fintype α] [DecidableEq α]
    (X : Finset α) (f : α → ℝ) : (∑ x, uniformMass X x * f x) = 𝔼 x ∈ X, f x := by
  simp only [uniformMass, ite_mul, zero_mul]
  rw [sum_ite, sum_const_zero, add_zero]
  simp only [filter_mem_eq_inter, univ_inter, ← mul_sum, expect_eq_sum_div_card]
  ring

theorem card_eq_rpow_sub_uniformDeficit_internal {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) : (X.card : ℝ) = (2 : ℝ) ^ ((Fintype.card ι : ℝ) - uniformDeficit X) := by
  have hp : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr hX
  dsimp [uniformDeficit]
  rw [sub_sub_cancel, Real.rpow_logb (by norm_num) (by norm_num) hp]

theorem uniformDeficit_le_iff_internal {ι : Type*} [Fintype ι] {X : Finset (ι → Bool)}
    (hX : X.Nonempty) {k : ℝ} : uniformDeficit X ≤ k ↔
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) ≤ X.card := by
  have he := Real.rpow_le_rpow_left_iff (x := (2 : ℝ))
    (y := (Fintype.card ι : ℝ) - k)
    (z := (Fintype.card ι : ℝ) - uniformDeficit X) (by norm_num)
  rw [← card_eq_rpow_sub_uniformDeficit_internal hX] at he
  exact he.trans (by constructor <;> intro h <;> linarith) |>.symm

theorem uniformMass_le_rpow_internal {ι : Type*} [Fintype ι]
    {X : Finset (ι → Bool)} (hX : X.Nonempty) {k : ℝ} (hdef : uniformDeficit X ≤ k)
    (x : ι → Bool) : uniformMass X x ≤ (2 : ℝ) ^ (k - Fintype.card ι) := by
  calc
    _ ≤ 1 / (X.card : ℝ) := by
      unfold uniformMass
      split_ifs
      · exact le_rfl
      · positivity
    _ = (2 : ℝ) ^ (uniformDeficit X - Fintype.card ι) := by
      rw [card_eq_rpow_sub_uniformDeficit_internal hX, one_div,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end Complexity.BooleanAnalysis
