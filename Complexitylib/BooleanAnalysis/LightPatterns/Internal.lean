/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.LightPatterns.Defs
public import Complexitylib.BooleanAnalysis.HarmonicMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Proof of Korten's improved light-patterns lemma

Theorem specialization for Lemma 10 of Oliver Korten, *Top-Down Lower Bounds
for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.

Transfer the downward-closed event that the harmonic transform is large,
then bound light patterns by the reciprocal-density Markov inequality.
The final step converts normalized marginal densities into probability masses
and counts, preserving the paper's real deficit parameter and constants.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

theorem harmonicTransform_sparse_good_probability_internal {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k) (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r
      (fun s => if 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s then 1 else 0) := by
  let B : ℝ := (2 : ℝ) ^ k
  let a : ℝ := 1 / (2 * Real.sqrt B)
  let A : Set (Fin n → Bool) := {s | 1 / (4 * B) ≤ harmonicTransform f s}
  have hB : 1 ≤ B := Real.one_le_rpow (by norm_num) (by linarith)
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : IsLowerSet A := by
    intro s t hst ht
    exact ht.trans (harmonicTransform_antitone hf fun i hi => Bool.le_iff_imp.mp (hst i) hi)
  have hA' : A.Nonempty := by
    refine ⟨fun _ => false, ?_⟩
    change 1 / (4 * B) ≤ harmonicTransform f (fun _ => false)
    rw [harmonicTransform_empty, hmean]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hrk : r ≤ r * k := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  have hr20 : r ≤ 1 / 20 := by nlinarith
  have hgood : a ≤ bernoulliAverage (1 / 4) (fun s => if s ∈ A then (1 : ℝ) else 0) :=
    harmonicTransform_good_probability hf hmean hB hbound
  have htransfer := (Real.rpow_le_rpow ha.le hgood (by positivity : 0 ≤ 5 * r)).trans
    (bernoulliAverage_lowerSet_transfer hA hA' hr hr20)
  have hlog : Real.log a = -(k / 2 + 1) * Real.log 2 := by
    dsimp [a]
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hBp.le]
    dsimp [B]
    rw [Real.log_rpow (by norm_num)]
    ring
  have he := Real.add_one_le_exp (Real.log a * (5 * r))
  rw [← Real.rpow_def_of_pos ha] at he
  rw [hlog] at he
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hloss : (k / 2 + 1) * (5 * r) * Real.log 2 ≤ (k / 2 + 1) * (5 * r) :=
    mul_le_of_le_one_right (by positivity) hlog2
  change 63 / 64 ≤ bernoulliAverage r (fun s => if s ∈ A then (1 : ℝ) else 0)
  nlinarith

theorem improved_light_patterns_density_internal {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, f x ≤ (2 : ℝ) ^ k) (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k) then 1 else 0) := by
  have ht : (2 : ℝ) ^ (-2 * k - 2) / (1 / (4 * (2 : ℝ) ^ k)) = (2 : ℝ) ^ (-k) := by
    have hfour : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [one_div, div_inv_eq_mul, hfour, ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  refine (harmonicTransform_sparse_good_probability_internal hf hmean hk hbound hr hr').trans
    (bernoulliAverage_mono hr hr1 fun s => ?_)
  by_cases hs : 1 / (4 * (2 : ℝ) ^ k) ≤ harmonicTransform f s
  · have hlight := coordinateMarginal_light_fraction_le hf s (by positivity) hs
      (by positivity : 0 ≤ (2 : ℝ) ^ (-2 * k - 2))
    rw [ht] at hlight
    simp only [ite_eq_left hs, ite_eq_left hlight, le_refl]
  · rw [ite_eq_right hs]
    split_ifs <;> norm_num

theorem coordinateMarginal_normalize_internal {n : ℕ} (mass : (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (z : {i // s i = true} → Bool) :
    coordinateMarginal (fun x => (2 : ℝ) ^ n * mass x) s z =
      (2 : ℝ) ^ Fintype.card {i // s i = true} * coordinateMass mass s z := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  have hc : (2 : ℝ) ^ n =
      (2 : ℝ) ^ Fintype.card {i // s i = true} *
        (Fintype.card ({i // s i ≠ true} → Bool) : ℝ) := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_prod] at h
    simp only [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast h
  unfold coordinateMarginal coordinateMass
  rw [Fintype.expect_eq_sum_div_card, ← mul_sum, hc]
  have hp : (0 : ℝ) < Fintype.card ({i // s i ≠ true} → Bool) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ({i // s i ≠ true} → Bool))
  field_simp

theorem improved_light_patterns_internal {n : ℕ} {mass : (Fin n → Bool) → ℝ}
    (hm : ∀ x, 0 ≤ mass x) (hmean : (∑ x, mass x) = 1) {k r : ℝ} (hk : 1 ≤ k)
    (hbound : ∀ x, mass x ≤ (2 : ℝ) ^ (k - n))
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (512 * k)) :
    63 / 64 ≤ bernoulliAverage r (fun s =>
      if ((univ.filter fun z => coordinateMass mass s z ≤
          (2 : ℝ) ^ (-(Fintype.card {i // s i = true} : ℝ) - 2 * k - 2)).card : ℝ) ≤
        (2 : ℝ) ^ ((Fintype.card {i // s i = true} : ℝ) - k) then 1 else 0) := by
  let f : (Fin n → Bool) → ℝ := fun x => (2 : ℝ) ^ n * mass x
  have hf : ∀ x, 0 ≤ f x := fun x => mul_nonneg (by positivity) (hm x)
  have hsum : (𝔼 x, f x) = 1 := by
    dsimp [f]
    rw [Fintype.expect_eq_sum_div_card, ← mul_sum, hmean]
    simp
  have hproduct : (2 : ℝ) ^ n * (2 : ℝ) ^ (k - n) = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hfb : ∀ x, f x ≤ (2 : ℝ) ^ k := by
    intro x
    exact (mul_le_mul_of_nonneg_left (hbound x) (by positivity)).trans_eq hproduct
  have hkr : r * (512 * k) ≤ 1 := (le_div_iff₀ (by positivity)).mp hr'
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hk)]
  refine (improved_light_patterns_density_internal hf hsum hk hfb hr hr').trans
    (bernoulliAverage_mono hr hr1 fun s => ?_)
  let m := Fintype.card {i // s i = true}
  have hp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hthreshold : (2 : ℝ) ^ m * (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2) =
      (2 : ℝ) ^ (-2 * k - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcount : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ m = (2 : ℝ) ^ ((m : ℝ) - k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have he (z : {i // s i = true} → Bool) :
      coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) ↔
        coordinateMass mass s z ≤ (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2) := by
    change coordinateMarginal (fun x => (2 : ℝ) ^ n * mass x) s z ≤ _ ↔ _
    rw [coordinateMarginal_normalize_internal, ← hthreshold]
    exact mul_le_mul_iff_right₀ hp
  have havg : (𝔼 z, if coordinateMarginal f s z ≤ (2 : ℝ) ^ (-2 * k - 2) then
        (1 : ℝ) else 0) =
      ((univ.filter fun z => coordinateMass mass s z ≤
        (2 : ℝ) ^ (-(m : ℝ) - 2 * k - 2)).card : ℝ) / (2 : ℝ) ^ m := by
    simp_rw [he]
    rw [Fintype.expect_eq_sum_div_card]
    simp [m]
  simp only [havg, div_le_iff₀ hp, hcount]
  exact le_rfl

theorem sum_coordinateMass_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mass : (ι → Bool) → ℝ) (s : ι → Bool) :
    (∑ z, coordinateMass mass s z) = ∑ x, mass x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  rw [← e.symm.sum_comp mass, Fintype.sum_prod_type]
  rfl

end Complexity.BooleanAnalysis
