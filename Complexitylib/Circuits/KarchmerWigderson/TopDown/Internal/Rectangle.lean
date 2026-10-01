/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Defs
public import Complexitylib.BooleanAnalysis.MirrorSets
public import Complexitylib.Circuits.KarchmerWigderson.TopDown.Internal.Sampling
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Maintaining the density rectangle through one message

A weighted pigeonhole argument bounds the entropy loss of a message cell.
Use the improved mirror set when the existing limit condition faces the wrong
speaker. A density limit at rate below `3/4` precludes a fixed separating coordinate.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem exists_large_message_fiber_internal {M : Type*} [Fintype M] [DecidableEq M]
    (X : Finset (ι → Bool)) (hX : X.Nonempty) (send : (ι → Bool) → M)
    {m : ℝ} (hm : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) :
    ∃ a : M, (X.filter fun x => send x = a).Nonempty ∧
      uniformDeficit (X.filter fun x => send x = a) ≤ uniformDeficit X + m := by
  obtain ⟨x, hx⟩ := hX
  have : Nonempty M := ⟨send x⟩
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast card_pos.mpr ⟨x, hx⟩
  let b : ℝ := X.card / (2 : ℝ) ^ m
  have hb : Fintype.card M • b ≤ (X.card : ℝ) := by
    rw [nsmul_eq_mul]
    calc
      _ ≤ (2 : ℝ) ^ m * b := mul_le_mul_of_nonneg_right hm (by dsimp [b]; positivity)
      _ = _ := by dsimp [b]; field_simp
  obtain ⟨a, _, ha⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := X) (t := univ) (f := send) (b := b) (fun _ _ => mem_univ _) univ_nonempty
    (by simpa only [card_univ] using hb)
  have hne : (X.filter fun x => send x = a).Nonempty := by
    apply card_pos.mp
    have hbpos : 0 < b := by dsimp [b]; positivity
    exact_mod_cast hbpos.trans_le ha
  refine ⟨a, hne, (uniformDeficit_le_iff hne).mpr ?_⟩
  convert ha using 1
  dsimp [b]
  rw [card_eq_rpow_sub_uniformDeficit (show X.Nonempty from ⟨x, hx⟩),
    ← Real.rpow_sub (by norm_num)]
  congr 1
  ring


theorem IsDensityLimit.agrees_internal {Y : Finset (ι → Bool)} {p k : ℝ} {x : ι → Bool}
    (hlim : IsDensityLimit Y p k x) (hp : 0 ≤ p) (hp' : p < 3 / 4) (i : ι) :
    ∃ y ∈ Y, y i = x i := by
  by_contra hn
  have hd (P : ι → Bool) (hi : P i ≠ true) : coordinateDensity Y P x = 0 := by
    rw [coordinateDensity_eq_expect]
    apply expect_eq_zero
    intro y _
    have hy : resample P x y ∉ Y := by
      intro hy
      apply hn
      exact ⟨resample P x y, hy, by simp [resample, hi]⟩
    simp [hy]
  have hpoint (P : ι → Bool) :
      (if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0) ≤
        if P i then 1 else 0 := by
    by_cases hi : P i = true
    · rw [ite_eq_left hi]
      split_ifs <;> norm_num
    · rw [ite_eq_right hi, hd P hi]
      have hn : ¬ (2 : ℝ) ^ (-k) ≤ 0 := not_le.mpr (by positivity)
      rw [ite_eq_right hn]
  have h := bernoulliAverage_mono hp (show p ≤ 1 by linarith) hpoint
  rw [bernoulliAverage_coordinate_internal] at h
  unfold IsDensityLimit at hlim
  linarith

theorem IsDensityLimit.mono_deficit_internal {Y : Finset (ι → Bool)} {p k k' : ℝ} {x : ι → Bool}
    (hlim : IsDensityLimit Y p k x) (hp : 0 ≤ p) (hp' : p ≤ 1) (hkk' : k ≤ k') :
    IsDensityLimit Y p k' x := by
  refine hlim.trans (bernoulliAverage_mono hp hp' fun P => ?_)
  by_cases h : (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x
  · have h' : (2 : ℝ) ^ (-k') ≤ coordinateDensity Y P x :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hkk')).trans h
    simp only [ite_eq_left h, ite_eq_left h', le_refl]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num


end Complexity.BooleanAnalysis

namespace Complexity.KarchmerWigderson

open BooleanAnalysis Finset
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem DensityRectangle.swap_internal {X Y : Finset (ι → Bool)} {p k : ℝ}
    (h : DensityRectangle X Y p k) : DensityRectangle Y X p k := by
  rcases h with ⟨hX, hY, hdX, hdY, r, hr, hrp, hl | hl⟩
  · exact ⟨hY, hX, hdY, hdX, r, hr, hrp, Or.inr hl⟩
  · exact ⟨hY, hX, hdY, hdX, r, hr, hrp, Or.inl hl⟩

theorem DensityRectangle.not_separated_internal {X Y : Finset (ι → Bool)} {p k : ℝ}
    (h : DensityRectangle X Y p k) (hp : p < 3 / 4) (i : ι) :
    ¬ ∀ x ∈ X, ∀ y ∈ Y, x i ≠ y i := by
  intro hsep
  rcases h with ⟨hX, hY, _, _, r, hr, hrp, hl | hl⟩
  · obtain ⟨x, hx⟩ := hX
    obtain ⟨y, hy, he⟩ := (hl x hx).agrees_internal hr.le (hrp.trans_lt hp) i
    exact hsep x hx y hy he.symm
  · obtain ⟨y, hy⟩ := hY
    obtain ⟨x, hx, he⟩ := (hl y hy).agrees_internal hr.le (hrp.trans_lt hp) i
    exact hsep x hx y hy he

theorem DensityRectangle.select_left_message_internal {M : Type*} [Fintype M] [DecidableEq M]
    {X Y : Finset (ι → Bool)} {p p' k k' m : ℝ} (h : DensityRectangle X Y p k)
    (send : (ι → Bool) → M) (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m)
    (hk : 1 ≤ k) (hkk : 194 * k ≤ k') (hcost : 2 * k + 2 + m ≤ k')
    (hscale : 32768 * k * p ≤ p') (hp' : p' ≤ 1 / 4) :
    ∃ (a : M) (X' : Finset (ι → Bool)), X' ⊆ X ∧ (∀ x ∈ X', send x = a) ∧
      DensityRectangle X' Y p' k' := by
  rcases h with ⟨hX, hY, hdX, hdY, r, hr, hrp, hl⟩
  have hkmono : k ≤ k' := by linarith
  have hp0 : 0 ≤ p := hr.le.trans hrp
  have hpmono : p ≤ p' := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hk)]
  have hselect (Z : Finset (ι → Bool)) (hZX : Z ⊆ X) (hZ : Z.Nonempty)
      (hdef : uniformDeficit Z + m ≤ k') (s : ℝ) (hs : 0 < s) (hsp : s ≤ p')
      (hlim : ∀ z ∈ Z, IsDensityLimit Y s k' z) :
      ∃ (a : M) (X' : Finset (ι → Bool)), X' ⊆ X ∧ (∀ x ∈ X', send x = a) ∧
        DensityRectangle X' Y p' k' := by
    obtain ⟨a, hne, hd⟩ := exists_large_message_fiber_internal Z hZ send hM
    refine ⟨a, Z.filter (fun x => send x = a), (filter_subset _ _).trans hZX,
      (fun x hx => (mem_filter.mp hx).2), hne, hY, hd.trans hdef, hdY.trans hkmono,
      s, hs, hsp, Or.inl ?_⟩
    exact fun x hx => hlim x (mem_filter.mp hx).1
  rcases hl with hl | hl
  · apply hselect X (Subset.refl _) hX (by linarith) r hr (hrp.trans hpmono)
    intro x hx
    exact (hl x hx).mono_deficit_internal hr.le (by linarith [hrp.trans hpmono]) hkmono
  · let q := 32768 * k * r
    have hqpos : 0 < q := by dsimp [q]; positivity
    have hqp : q ≤ p' :=
      (mul_le_mul_of_nonneg_left hrp (show 0 ≤ 32768 * k by positivity)).trans hscale
    obtain ⟨Z, hZX, hZ, hdef, hlim⟩ := improved_mirror_set Y X hY hk hdY hr rfl
      (show q ≤ 1 / 2 by linarith) hl
    apply hselect Z hZX hZ (by linarith) q hqpos hqp
    intro z hz
    exact (hlim z hz).mono_deficit_internal hqpos.le (by linarith) hkk

end Complexity.KarchmerWigderson
