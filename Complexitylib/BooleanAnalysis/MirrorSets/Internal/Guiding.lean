/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.MirrorSets.Defs
public import Complexitylib.BooleanAnalysis.MirrorSets.Internal.Completion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Guided distributions and the improved mirror set

On a sufficiently dense fiber, sample uniformly from its intersection with `Y`;
on the remaining fibers, sample uniformly from the whole fiber. The density of
this sampling rule is at most `2^k`. This is a distributional variant of the
fixed-size guiding sets in Oliver Korten's proof, avoiding a rounding operation.

The completion estimate bounds the guided failure probability by `1/16`.
Intersecting `Y` with the `(q,194*k)`-limits of `X` gives a nonempty mirror set
of deficit at most `2*k+2`, with `q = 32768*k*p`.

Source: Oliver Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221
(2026), https://eccc.weizmann.ac.il/report/2026/221/, Sections 3--4.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Density of the guiding rule relative to uniform coordinate modifications.
Dense fibers are restricted to `Y`; the other fibers are left uniform. -/
noncomputable def guidingDensity (Y : Finset (ι → Bool)) (k : ℝ) (P x y : ι → Bool) : ℝ :=
  if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then
    (if resample P x y ∈ Y then 1 else 0) / coordinateDensity Y P x else 1

/-- Expectation of a test function after a guided modification of a uniform
point of `X`, using a rate-`p` coordinate mask and deficit parameter `k`. -/
noncomputable def guidedAverage (X Y : Finset (ι → Bool)) (p k : ℝ)
    (f : (ι → Bool) → ℝ) : ℝ :=
  𝔼 x ∈ X, bernoulliAverage p (fun P =>
    𝔼 y, guidingDensity Y k P x y * f (resample P x y))

theorem guidingDensity_nonneg_internal (Y : Finset (ι → Bool)) (k : ℝ) (P x y : ι → Bool) :
    0 ≤ guidingDensity Y k P x y := by
  have hd := coordinateDensity_nonneg Y P x
  unfold guidingDensity
  split_ifs <;> positivity

theorem expect_guidingDensity_internal (Y : Finset (ι → Bool)) (k : ℝ) (P x : ι → Bool) :
    (𝔼 y, guidingDensity Y k P x y) = 1 := by
  unfold guidingDensity
  split_ifs with h
  · rw [← expect_div, ← coordinateDensity_eq_expect]
    exact div_self (ne_of_gt (lt_of_lt_of_le (by positivity) h))
  · exact Fintype.expect_const _

theorem guidingDensity_le_internal (Y : Finset (ι → Bool)) {k : ℝ} (hk : 0 ≤ k)
    (P x y : ι → Bool) : guidingDensity Y k P x y ≤ (2 : ℝ) ^ k := by
  unfold guidingDensity
  split_ifs with h hy
  · apply (div_le_iff₀ (lt_of_lt_of_le (by positivity) h)).mpr
    have he : (2 : ℝ) ^ (-k) * (2 : ℝ) ^ k = 1 := by
      rw [← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero]
    nlinarith [mul_le_mul_of_nonneg_right h (show (0 : ℝ) ≤ 2 ^ k by positivity)]
  · simp only [zero_div]
    positivity
  · exact Real.one_le_rpow (by norm_num) hk

theorem guidedAverage_const_internal (X Y : Finset (ι → Bool)) (hX : X.Nonempty) (p k c : ℝ) :
    guidedAverage X Y p k (fun _ => c) = c := by
  unfold guidedAverage
  simp_rw [← expect_mul, expect_guidingDensity_internal, one_mul, bernoulliAverage_const]
  exact expect_const hX c

theorem guidedAverage_mono_internal (X Y : Finset (ι → Bool)) {p k : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {f g : (ι → Bool) → ℝ} (hfg : ∀ z, f z ≤ g z) :
    guidedAverage X Y p k f ≤ guidedAverage X Y p k g := by
  apply expect_le_expect
  intro x _
  apply bernoulliAverage_mono hp hp'
  intro P
  exact expect_le_expect fun y _ =>
    mul_le_mul_of_nonneg_left (hfg _) (guidingDensity_nonneg_internal Y k P x y)

theorem expect_resample_internal (f : (ι → Bool) → ℝ) (P : ι → Bool) :
    (𝔼 x, 𝔼 y, f (resample P x y)) = 𝔼 z, f z := by
  have he (x : ι → Bool) : (𝔼 y, f (resample P x y)) =
      projectionAverage f (fun i => !P i) x := by
    unfold projectionAverage
    apply expect_congr rfl
    intro y _
    apply congrArg f
    funext i
    cases hp : P i <;> simp [resample, hp]
  simp_rw [he]
  exact (expect_coordinateMarginal_comp_internal f (fun i => !P i) id).trans
    (expect_coordinateMarginal f _)

theorem sum_expect_resample_internal (f : (ι → Bool) → ℝ) (P : ι → Bool) :
    (∑ x, 𝔼 y, f (resample P x y)) = ∑ z, f z := by
  rw [← Fintype.card_mul_expect, expect_resample_internal, Fintype.card_mul_expect]

theorem expect_resample_subset_le_internal (X : Finset (ι → Bool)) (f : (ι → Bool) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (P : ι → Bool) :
    (𝔼 x ∈ X, 𝔼 y, f (resample P x y)) ≤ (∑ z, f z) / (X.card : ℝ) := by
  rw [expect_eq_sum_div_card]
  have hs : (∑ x ∈ X, 𝔼 y, f (resample P x y)) ≤ ∑ x, 𝔼 y, f (resample P x y) := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ X)
      (fun x _ _ => expect_nonneg (fun y _ => hf _))
  rw [sum_expect_resample_internal] at hs
  exact div_le_div_of_nonneg_right hs (by positivity)

theorem guidedAverage_bound_internal (X Y : Finset (ι → Bool)) {p k : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hk : 0 ≤ k) (f : (ι → Bool) → ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    guidedAverage X Y p k f ≤ (2 : ℝ) ^ k * (∑ z, f z) / X.card := by
  have hm : guidedAverage X Y p k f ≤
      (2 : ℝ) ^ k * bernoulliAverage p (fun P => 𝔼 x ∈ X, 𝔼 y, f (resample P x y)) := by
    unfold guidedAverage
    rw [bernoulliAverage_expect_comm_internal, mul_expect]
    apply expect_le_expect
    intro x _
    rw [← bernoulliAverage_mul_internal]
    apply bernoulliAverage_mono hp hp'
    intro P
    rw [mul_expect]
    exact expect_le_expect fun y _ =>
      mul_le_mul_of_nonneg_right (guidingDensity_le_internal Y hk P x y) (hf _)
  have hb := bernoulliAverage_mono hp hp' (expect_resample_subset_le_internal X f hf)
  rw [bernoulliAverage_const] at hb
  exact hm.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
    (mul_div_assoc _ _ _).symm)

theorem guidingDensity_hits_internal (Y : Finset (ι → Bool)) (k : ℝ) (P x : ι → Bool) :
    (if (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x then (1 : ℝ) else 0) ≤
      𝔼 y, guidingDensity Y k P x y * (if resample P x y ∈ Y then 1 else 0) := by
  by_cases h : (2 : ℝ) ^ (-k) ≤ coordinateDensity Y P x
  · have he (y : ι → Bool) : guidingDensity Y k P x y *
        (if resample P x y ∈ Y then 1 else 0) = guidingDensity Y k P x y := by
      unfold guidingDensity
      simp only [ite_eq_left h]
      split_ifs <;> simp
    simp_rw [he, expect_guidingDensity_internal, ite_eq_left h]
    exact le_rfl
  · rw [ite_eq_right h]
    exact expect_nonneg fun y _ => mul_nonneg (guidingDensity_nonneg_internal Y k P x y)
      (by split_ifs <;> norm_num)

theorem guidedAverage_hits_internal (X Y : Finset (ι → Bool)) (hX : X.Nonempty) {p k : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    3 / 4 ≤ guidedAverage X Y p k (fun z => if z ∈ Y then 1 else 0) := by
  have hpoint (x : ι → Bool) (hx : x ∈ X) : 3 / 4 ≤ bernoulliAverage p (fun P =>
      𝔼 y, guidingDensity Y k P x y * (if resample P x y ∈ Y then 1 else 0)) :=
    (hlim x hx).trans (bernoulliAverage_mono hp hp' (fun P => guidingDensity_hits_internal Y k P x))
  simpa only [guidedAverage, expect_const hX] using expect_le_expect (s := X) hpoint

theorem guidedAverage_linear_internal (X Y : Finset (ι → Bool)) (p k a b : ℝ)
    (f g : (ι → Bool) → ℝ) :
    guidedAverage X Y p k (fun z => a * f z + b * g z) =
      a * guidedAverage X Y p k f + b * guidedAverage X Y p k g := by
  unfold guidedAverage
  have he (x P y : ι → Bool) : guidingDensity Y k P x y *
      (a * f (resample P x y) + b * g (resample P x y)) =
        a * (guidingDensity Y k P x y * f (resample P x y)) +
        b * (guidingDensity Y k P x y * g (resample P x y)) := by ring
  simp_rw [he, expect_add_distrib, ← mul_expect, bernoulliAverage_linear_internal]
  rw [expect_add_distrib, ← mul_expect, ← mul_expect]

theorem guidedAverage_bernoulli_internal (X Y : Finset (ι → Bool)) (p q k : ℝ)
    (f : (ι → Bool) → (ι → Bool) → ℝ) :
    guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q => f Q z)) =
      bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
        𝔼 x ∈ X, 𝔼 y, guidingDensity Y k P x y * f Q (resample P x y))) := by
  unfold guidedAverage
  simp_rw [← bernoulliAverage_mul_internal, ← bernoulliAverage_expect_comm_internal]

theorem guidingDensity_small_event_internal (Y : Finset (ι → Bool)) {k : ℝ} (hk : 0 ≤ k)
    (P x : ι → Bool) (f : (ι → Bool) → ℝ) (hf : ∀ y, 0 ≤ f y) (hf' : ∀ y, f y ≤ 1) :
    (𝔼 y, guidingDensity Y k P x y * f y) ≤
      65 / 64 - (if (𝔼 y, f y) ≤ (2 : ℝ) ^ (-k - 6) then (1 : ℝ) else 0) := by
  have hone : (𝔼 y, guidingDensity Y k P x y * f y) ≤ 1 := by
    rw [← expect_guidingDensity_internal Y k P x]
    exact expect_le_expect fun y _ => mul_le_of_le_one_right
      (guidingDensity_nonneg_internal Y k P x y) (hf' y)
  by_cases hsmall : (𝔼 y, f y) ≤ (2 : ℝ) ^ (-k - 6)
  · have hcap : (𝔼 y, guidingDensity Y k P x y * f y) ≤
        (2 : ℝ) ^ k * (𝔼 y, f y) := by
      rw [mul_expect]
      exact expect_le_expect fun y _ =>
        mul_le_mul_of_nonneg_right (guidingDensity_le_internal Y hk P x y) (hf y)
    have he : (2 : ℝ) ^ k * (2 : ℝ) ^ (-k - 6) = 1 / 64 := by
      rw [← Real.rpow_add (by norm_num), show k + (-k - 6) = (-6 : ℝ) by ring]
      norm_num
    have hh := hcap.trans ((mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq he)
    rw [ite_eq_left hsmall]
    linarith
  · rw [ite_eq_right hsmall]
    linarith

theorem guidedAverage_bad_completion_internal (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2) :
    guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q =>
      if coordinateDensity X Q z < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0)) ≤ 1 / 16 := by
  have hqp : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  let f (Q z : ι → Bool) : ℝ :=
    if coordinateDensity X Q z < (2 : ℝ) ^ (-194 * k) then 1 else 0
  have hm : guidedAverage X Y p k (fun z => bernoulliAverage q (fun Q => f Q z)) ≤
      bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
        𝔼 x ∈ X, (65 / 64 - (if (𝔼 y, f Q (resample P x y)) ≤ (2 : ℝ) ^ (-k - 6)
          then (1 : ℝ) else 0)))) := by
    rw [guidedAverage_bernoulli_internal]
    apply bernoulliAverage_mono hp.le (hpq.trans hq1)
    intro P
    apply bernoulliAverage_mono hqp.le hq1
    intro Q
    apply expect_le_expect
    intro x _
    exact guidingDensity_small_event_internal Y (by linarith) P x (fun y => f Q (resample P x y))
      (by intro y; dsimp [f]; split_ifs <;> norm_num)
      (by intro y; dsimp [f]; split_ifs <;> norm_num)
  simp_rw [expect_sub_distrib, expect_const hX, bernoulliAverage_sub_internal,
    bernoulliAverage_const] at hm
  have hg := mirror_bad_modifications_probability_internal X hX hk hdef hp hq hq'
  dsimp only [f] at hm
  linarith

theorem densityLimit_complement_internal (X : Finset (ι → Bool)) (q t : ℝ) (z : ι → Bool) :
    bernoulliAverage q (fun Q => if coordinateDensity X Q z < (2 : ℝ) ^ (-t) then
      (1 : ℝ) else 0) = 1 - bernoulliAverage q
        (fun Q => if (2 : ℝ) ^ (-t) ≤ coordinateDensity X Q z then (1 : ℝ) else 0) := by
  have he (Q : ι → Bool) : (if coordinateDensity X Q z < (2 : ℝ) ^ (-t) then
      (1 : ℝ) else 0) = 1 - (if (2 : ℝ) ^ (-t) ≤ coordinateDensity X Q z then 1 else 0) := by
    split_ifs <;> linarith
  simp_rw [he, bernoulliAverage_sub_internal, bernoulliAverage_const]

theorem guidedAverage_mirror_mass_internal (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2)
    (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    1 / 4 ≤ guidedAverage X Y p k
      (fun z => if z ∈ Y ∧ IsDensityLimit X q (194 * k) z then (1 : ℝ) else 0) := by
  have hqp : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  let bad (z : ι → Bool) : ℝ := bernoulliAverage q (fun Q =>
    if coordinateDensity X Q z < (2 : ℝ) ^ (-(194 * k)) then (1 : ℝ) else 0)
  have hbad (z : ι → Bool) : 0 ≤ bad z := by
    have h := bernoulliAverage_mono hqp.le hq1 (f := fun _ => 0)
      (g := fun Q => if coordinateDensity X Q z < (2 : ℝ) ^ (-(194 * k)) then 1 else 0)
      (by intro Q; split_ifs <;> norm_num)
    simpa only [bernoulliAverage_const] using h
  have hpoint (z : ι → Bool) : (if z ∈ Y then (1 : ℝ) else 0) ≤
      1 * (if z ∈ Y ∧ IsDensityLimit X q (194 * k) z then 1 else 0) + 4 * bad z := by
    by_cases hy : z ∈ Y
    · by_cases hl : IsDensityLimit X q (194 * k) z
      · simp only [hy, hl, and_self, ite_true, one_mul]
        nlinarith [hbad z]
      · have hh : 1 / 4 < bad z := by
          dsimp only [bad]
          rw [densityLimit_complement_internal]
          unfold IsDensityLimit at hl
          linarith
        simp only [hy, hl, and_false, ite_true, ite_false, mul_zero, zero_add]
        linarith
    · simp only [hy, false_and, ite_false, mul_zero, zero_add]
      nlinarith [hbad z]
  have hm := guidedAverage_mono_internal X Y (k := k) hp.le (hpq.trans hq1) hpoint
  rw [guidedAverage_linear_internal, one_mul] at hm
  have hhit := guidedAverage_hits_internal X Y hX hp.le (hpq.trans hq1) hlim
  have hloss : guidedAverage X Y p k bad ≤ 1 / 16 := by
    simpa only [bad, neg_mul] using guidedAverage_bad_completion_internal X Y hX hk hdef hp hq hq'
  linarith

theorem improved_mirror_set_internal (X Y : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2)
    (hlim : ∀ x ∈ X, IsDensityLimit Y p k x) :
    ∃ Y' : Finset (ι → Bool), Y' ⊆ Y ∧ Y'.Nonempty ∧ uniformDeficit Y' ≤ 2 * k + 2 ∧
      ∀ y ∈ Y', IsDensityLimit X q (194 * k) y := by
  let A := Y.filter (IsDensityLimit X q (194 * k))
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  have hm : 1 / 4 ≤ guidedAverage X Y p k (fun z => if z ∈ A then (1 : ℝ) else 0) := by
    simpa only [A, mem_filter] using
      guidedAverage_mirror_mass_internal X Y hX hk hdef hp hq hq' hlim
  have hb : guidedAverage X Y p k (fun z => if z ∈ A then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ k * A.card / X.card := by
    simpa using guidedAverage_bound_internal X Y hp.le (hpq.trans hq1) (show 0 ≤ k by linarith)
      (fun z => if z ∈ A then (1 : ℝ) else 0) (by intro z; split_ifs <;> norm_num)
  have hxpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hxcount := (uniformDeficit_le_iff hX).mp hdef
  have hprod : (4 * (2 : ℝ) ^ k) * (2 : ℝ) ^ ((Fintype.card ι : ℝ) - (2 * k + 2)) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - k) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcard : (2 : ℝ) ^ ((Fintype.card ι : ℝ) - (2 * k + 2)) ≤ A.card := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * (2 : ℝ) ^ k by positivity)).mp
    rw [hprod]
    have hh := (le_div_iff₀ hxpos).mp (hm.trans hb)
    nlinarith
  have hA : A.Nonempty := by
    apply card_pos.mp
    have hpos := (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num)
      ((Fintype.card ι : ℝ) - (2 * k + 2))).trans_le hcard
    exact_mod_cast hpos
  exact ⟨A, filter_subset _ _, hA, (uniformDeficit_le_iff hA).mpr hcard,
    fun y hy => (mem_filter.mp hy).2⟩

end Complexity.BooleanAnalysis
