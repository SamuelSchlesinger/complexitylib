/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.HarmonicMean.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite harmonic mean: proof internals

The variational formula of Korten (2026), Lemma 11, is proved for every
nonempty finite type. Completing the square gives the lower bound, and an
explicit weight attains it, including when an entry vanishes.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
theorem harmonicMean_nonneg_internal {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ harmonicMean f := by
  unfold harmonicMean
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))

theorem harmonicMean_le_energy_internal {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hw : (𝔼 x, w x) = 1) : harmonicMean f ≤ 𝔼 x, f x * w x ^ 2 := by
  classical
  by_cases hz : ∃ x, f x = 0
  · rw [harmonicMean, ite_eq_left hz]
    exact expect_nonneg fun x _ => mul_nonneg (hf x) (sq_nonneg _)
  have hpos : ∀ x, 0 < f x := fun x => lt_of_le_of_ne (hf x) (Ne.symm (by
    intro h; exact hz ⟨x, h⟩))
  have he : (𝔼 x, (f x)⁻¹) ≠ 0 := ne_of_gt
    (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty)
  let h := (𝔼 x, (f x)⁻¹)⁻¹
  have hs := expect_nonneg (s := univ)
    (fun x _ => mul_nonneg (hf x) (sq_nonneg (w x - h / f x)))
  have hid (x : α) : f x * (w x - h / f x) ^ 2 =
      f x * w x ^ 2 - 2 * h * w x + h ^ 2 * (f x)⁻¹ := by
    field_simp [ne_of_gt (hpos x)]
    ring
  simp_rw [hid, expect_add_distrib, expect_sub_distrib, ← mul_expect] at hs
  rw [hw] at hs
  have hh : h ^ 2 * (𝔼 x, (f x)⁻¹) = h := by
    dsimp [h]
    field_simp
  rw [hh] at hs
  rw [harmonicMean, ite_eq_right hz]
  dsimp [h] at hs
  linarith

theorem harmonicMean_exists_weight_internal {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∃ w : α → ℝ, (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧
      (𝔼 x, f x * w x ^ 2) = harmonicMean f := by
  classical
  by_cases hz : ∃ x, f x = 0
  · obtain ⟨a, ha⟩ := hz
    refine ⟨fun x => if x = a then Fintype.card α else 0, ?_, ?_, ?_⟩
    · intro x; dsimp only; split_ifs <;> positivity
    · rw [Fintype.expect_eq_sum_div_card]
      simp [Fintype.card_ne_zero]
    · rw [harmonicMean, ite_eq_left ⟨a, ha⟩]
      apply expect_eq_zero
      intro x _
      by_cases hx : x = a <;> simp [hx, ha]
  · have hpos : ∀ x, 0 < f x := fun x => lt_of_le_of_ne (hf x) (Ne.symm (by
      intro h; exact hz ⟨x, h⟩))
    have he : (𝔼 x, (f x)⁻¹) ≠ 0 := ne_of_gt
      (expect_pos (fun x _ => inv_pos.mpr (hpos x)) univ_nonempty)
    let h := (𝔼 x, (f x)⁻¹)⁻¹
    refine ⟨fun x => h * (f x)⁻¹, ?_, ?_, ?_⟩
    · intro x
      exact mul_nonneg (inv_nonneg.mpr
        (expect_nonneg fun x _ => inv_nonneg.mpr (hf x))) (inv_nonneg.mpr (hf x))
    · rw [← mul_expect]
      exact inv_mul_cancel₀ he
    · have hid (x : α) : f x * (h * (f x)⁻¹) ^ 2 = h ^ 2 * (f x)⁻¹ := by
        field_simp [ne_of_gt (hpos x)]
      simp_rw [hid, ← mul_expect]
      rw [harmonicMean, ite_eq_right hz]
      dsimp [h]
      field_simp

theorem harmonicMean_variational_internal {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f = sInf {a : ℝ | ∃ w : α → ℝ,
      (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧ (𝔼 x, f x * w x ^ 2) = a} := by
  symm
  apply IsLeast.csInf_eq
  constructor
  · exact harmonicMean_exists_weight_internal hf
  · rintro _ ⟨w, _, hw, rfl⟩
    exact harmonicMean_le_energy_internal hf hw

theorem harmonicMean_mono_internal {f g : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    harmonicMean f ≤ harmonicMean g := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight_internal
    (fun x => (hf x).trans (hfg x))
  rw [← he]
  exact (harmonicMean_le_energy_internal hf hw).trans
    (expect_le_expect fun x _ => mul_le_mul_of_nonneg_right (hfg x) (sq_nonneg _))

theorem harmonicMean_concave_internal {f g : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    t * harmonicMean f + (1 - t) * harmonicMean g ≤
      harmonicMean (fun x => t * f x + (1 - t) * g x) := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight_internal
    (fun x => add_nonneg (mul_nonneg ht (hf x)) (mul_nonneg (sub_nonneg.mpr ht') (hg x)))
  calc
    _ ≤ t * (𝔼 x, f x * w x ^ 2) + (1 - t) * (𝔼 x, g x * w x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (harmonicMean_le_energy_internal hf hw) ht)
        (mul_le_mul_of_nonneg_left (harmonicMean_le_energy_internal hg hw)
          (sub_nonneg.mpr ht'))
    _ = 𝔼 x, (t * f x + (1 - t) * g x) * w x ^ 2 := by
      simp_rw [add_mul, mul_assoc, expect_add_distrib, ← mul_expect]
    _ = _ := he

theorem harmonicMean_le_expect_internal {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f ≤ 𝔼 x, f x := by
  simpa using harmonicMean_le_energy_internal (w := fun _ => 1) hf (by simp)

theorem harmonicMean_const_internal (c : ℝ) :
    harmonicMean (fun _ : α => c) = c := by
  classical
  by_cases hc : c = 0 <;> simp [harmonicMean, hc]

omit [Nonempty α] in
theorem harmonicMean_equiv_internal {β : Type*} [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : harmonicMean (fun x => f (e x)) = harmonicMean f := by
  classical
  have hz : (∃ x, f (e x) = 0) ↔ ∃ y, f y = 0 := by
    constructor
    · rintro ⟨x, hx⟩; exact ⟨e x, hx⟩
    · rintro ⟨y, hy⟩; exact ⟨e.symm y, by simpa⟩
  simp only [harmonicMean, hz]
  rw [Fintype.expect_equiv e (fun x => (f (e x))⁻¹) (fun y => (f y)⁻¹)
    (fun _ => rfl)]

theorem harmonicMean_average_internal {β : Type*} [Fintype β]
    {f : β → α → ℝ} (hf : ∀ y x, 0 ≤ f y x) :
    (𝔼 y, harmonicMean (f y)) ≤ harmonicMean (fun x => 𝔼 y, f y x) := by
  obtain ⟨w, _, hw, he⟩ := harmonicMean_exists_weight_internal
    (fun x => expect_nonneg fun y _ => hf y x)
  calc
    _ ≤ 𝔼 y, 𝔼 x, f y x * w x ^ 2 :=
      expect_le_expect fun y _ => harmonicMean_le_energy_internal (hf y) hw
    _ = 𝔼 x, (𝔼 y, f y x) * w x ^ 2 := by
      rw [expect_comm]
      simp_rw [expect_mul]
    _ = _ := he

omit [Nonempty α] in
theorem expect_pair_internal {β : Type*} [Fintype β] (f : α × β → ℝ) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 b, f (a, b) := by
  simpa only [univ_product_univ] using expect_product univ univ f

theorem expect_bool_internal (f : Bool → ℝ) :
    (𝔼 b, f b) = (f false + f true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool]
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  ring

theorem harmonicMean_pair_internal {f : Bool → α → ℝ} (hf : ∀ b x, 0 ≤ f b x) :
    harmonicMean (fun x : Bool × α => f x.1 x.2) =
      2 * harmonicMean (f false) * harmonicMean (f true) /
        (harmonicMean (f false) + harmonicMean (f true)) := by
  classical
  by_cases h0 : ∃ x, f false x = 0
  · have hz : ∃ x : Bool × α, f x.1 x.2 = 0 := by
      obtain ⟨x, hx⟩ := h0; exact ⟨(false, x), hx⟩
    simp [harmonicMean, h0, hz]
  by_cases h1 : ∃ x, f true x = 0
  · have hz : ∃ x : Bool × α, f x.1 x.2 = 0 := by
      obtain ⟨x, hx⟩ := h1; exact ⟨(true, x), hx⟩
    simp [harmonicMean, h1, hz]
  have hz : ¬ ∃ x : Bool × α, f x.1 x.2 = 0 := by
    rintro ⟨⟨b, x⟩, hx⟩
    cases b
    · exact h0 ⟨x, hx⟩
    · exact h1 ⟨x, hx⟩
  have hp (b : Bool) : 0 < 𝔼 x, (f b x)⁻¹ := by
    apply expect_pos _ univ_nonempty
    intro x _
    apply inv_pos.mpr
    have hn : f b x ≠ 0 := fun h => hz ⟨(b, x), h⟩
    exact lt_of_le_of_ne (hf b x) hn.symm
  simp only [harmonicMean, ite_eq_right hz, ite_eq_right h0, ite_eq_right h1]
  rw [expect_pair_internal, expect_bool_internal]
  have hsum := add_pos (hp false) (hp true)
  field_simp [ne_of_gt (hp false), ne_of_gt (hp true), ne_of_gt hsum]
  simpa only [one_div, add_comm] using (div_self (ne_of_gt hsum)).symm

theorem harmonicMean_light_fraction_le_internal {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {a b : ℝ} (ha : 0 < a) (ha' : a ≤ harmonicMean f) (hb : 0 ≤ b) :
    (𝔼 x, if f x ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  classical
  have hz : ¬ ∃ x, f x = 0 := by
    intro h
    rw [harmonicMean, ite_eq_left h] at ha'
    exact (not_le_of_gt ha) ha'
  have hp (x : α) : 0 < f x :=
    lt_of_le_of_ne (hf x) (Ne.symm fun h => hz ⟨x, h⟩)
  have he : 0 < 𝔼 x, (f x)⁻¹ :=
    expect_pos (fun x _ => inv_pos.mpr (hp x)) univ_nonempty
  have hinv : (𝔼 x, (f x)⁻¹) ≤ 1 / a := by
    rw [harmonicMean, ite_eq_right hz, ← one_div] at ha'
    have hmul := (le_div_iff₀ he).mp ha'
    apply (le_div_iff₀ ha).mpr
    linarith
  calc
    _ ≤ 𝔼 x, b * (f x)⁻¹ := by
      apply expect_le_expect
      intro x _
      split_ifs with h
      · rw [← div_eq_mul_inv]
        exact (one_le_div (hp x)).mpr h
      · exact mul_nonneg hb (inv_nonneg.mpr (hf x))
    _ = b * (𝔼 x, (f x)⁻¹) := (mul_expect _ _ _).symm
    _ ≤ b * (1 / a) := mul_le_mul_of_nonneg_left hinv hb
    _ = _ := by ring

end Complexity.BooleanAnalysis
