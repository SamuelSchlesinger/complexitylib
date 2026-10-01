/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.CoordinateSampling
public import Complexitylib.BooleanAnalysis.Fibers
public import Complexitylib.BooleanAnalysis.LightPatterns
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Completion density in Korten's improved mirror-set argument

Apply the entropy lemma and improved light-patterns lemma inside the sampled
union fiber. The exact conditional sampling law yields the `31/32` estimate
for the fraction of first-stage modifications with low completion density.

Source: Oliver Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221
(2026), https://eccc.weizmann.ac.il/report/2026/221/, Sections 3--4.
The explicit constants here are `q = 32768*k*p` and completion deficit `194*k`.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem projectionAverage_const_mul_internal (a : ℝ) (f : (ι → Bool) → ℝ) (s x : ι → Bool) :
    projectionAverage (fun y => a * f y) s x = a * projectionAverage f s x := by
  exact (mul_expect _ _ _).symm

theorem projectionAverage_fiber_internal (f : (ι → Bool) → ℝ) (s x : ι → Bool)
    (R u : {i // s i = true} → Bool) :
    projectionAverage (fun z => f (completePattern s x z)) R u =
      projectionAverage f (fun i => if h : s i = true then R ⟨i, h⟩ else true)
        (completePattern s x u) := by
  unfold projectionAverage
  rw [← expect_restrict_coordinates s]
  apply expect_congr rfl
  intro y _
  apply congrArg f
  funext i
  by_cases hs : s i = true
  · simp only [completePattern, dite_eq_left hs]
  · simp [completePattern, hs]

theorem coordinateDensity_eq_projection_internal (X : Finset (ι → Bool)) (s x : ι → Bool) :
    coordinateDensity X s x =
      projectionAverage (fun y => if y ∈ X then 1 else 0) (fun i => !s i) x := by
  rw [coordinateDensity_eq_expect]
  unfold projectionAverage
  apply expect_congr rfl
  intro y _
  apply congrArg (fun t => if t ∈ X then (1 : ℝ) else 0)
  funext i
  cases hs : s i <;> simp [resample, hs]

theorem projectionAverage_uniformDensity_fiber_internal (X : Finset (ι → Bool)) (s x : ι → Bool)
    (hX : (coordinateFiber X s x).Nonempty) (R u : {i // s i = true} → Bool) :
    projectionAverage (uniformDensity (coordinateFiber X s x)) R u =
      (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) *
        coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
          (completePattern s x u) := by
  have he : uniformDensity (coordinateFiber X s x) = fun z =>
      (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) *
        (if completePattern s x z ∈ X then 1 else 0) := by
    funext z
    rw [uniformDensity_eq_deficit hX]
    simp only [coordinateFiber, mem_filter, mem_univ, true_and]
  rw [he, projectionAverage_const_mul_internal,
    projectionAverage_fiber_internal (fun y => if y ∈ X then 1 else 0),
    coordinateDensity_eq_projection_internal]
  congr 2
  funext i
  by_cases hs : s i = true <;> simp [hs]

theorem expect_coordinateMarginal_comp_internal (f : (ι → Bool) → ℝ) (s : ι → Bool) (g : ℝ → ℝ) :
    (𝔼 x, g (projectionAverage f s x)) = 𝔼 z, g (coordinateMarginal f s z) := by
  simp_rw [projectionAverage_eq_coordinateMarginal]
  exact expect_restrict_coordinates s (fun z => g (coordinateMarginal f s z))

theorem coordinateFiber_light_patterns_internal (X : Finset (ι → Bool)) (hX : X.Nonempty)
    (s : ι → Bool) {k r : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (32768 * k)) :
    31 / 32 ≤ 𝔼 x ∈ X, bernoulliAverage r (fun R =>
      if uniformDeficit (coordinateFiber X s x) ≤ 64 * k ∧
        (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
          (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
        then 1 else 0) := by
  have hpoint (x : ι → Bool) (hx : x ∈ X) :
      63 / 64 * (if uniformDeficit (coordinateFiber X s x) ≤ 64 * k then (1 : ℝ) else 0) ≤
        bernoulliAverage r (fun R =>
          if uniformDeficit (coordinateFiber X s x) ≤ 64 * k ∧
            (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
              (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
            then 1 else 0) := by
    by_cases hd : uniformDeficit (coordinateFiber X s x) ≤ 64 * k
    · simp only [hd, true_and, ite_true, mul_one]
      have hne := coordinateFiber_nonempty s hx
      have ht := improved_light_patterns_density
        (fun z => mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ Fintype.card {i // s i = true})
          (uniformMass_nonneg (coordinateFiber X s x) z))
        (expect_uniformDensity hne) (show (1 : ℝ) ≤ 64 * k by linarith)
        (uniformDensity_le_rpow hne hd) hr
        (show r ≤ 1 / (512 * (64 * k)) by convert hr' using 1; ring)
      rw [show (-2 : ℝ) * (64 * k) - 2 = -128 * k - 2 by ring,
        show -(64 * k) = -64 * k by ring] at ht
      exact ht
    · simp only [hd, false_and, ite_false, mul_zero, bernoulliAverage_const]
      exact le_rfl
  have hl := expect_le_expect (s := X) hpoint
  rw [← mul_expect] at hl
  have hg := coordinateFiber_good_probability X hX s (show 0 < k by linarith) hdef
  nlinarith

theorem fiber_completion_density_internal (X : Finset (ι → Bool)) (s x : ι → Bool)
    (hX : (coordinateFiber X s x).Nonempty) (R : {i // s i = true} → Bool)
    {k : ℝ} (hk : 1 ≤ k) (hd : uniformDeficit (coordinateFiber X s x) ≤ 64 * k)
    (hl : (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X s x)) R z ≤
      (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)) :
    (𝔼 u, if coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
      (completePattern s x u) < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-k - 6) := by
  have hpoint (u : {i // s i = true} → Bool) :
      (if coordinateDensity X (fun i => if h : s i = true then !R ⟨i, h⟩ else false)
        (completePattern s x u) < (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤
        if projectionAverage (uniformDensity (coordinateFiber X s x)) R u ≤
          (2 : ℝ) ^ (-128 * k - 2) then 1 else 0 := by
    split_ifs with hb hl
    · exact le_rfl
    · exfalso
      apply hl
      have he := projectionAverage_uniformDensity_fiber_internal X s x hX R u
      rw [he]
      calc
        _ ≤ (2 : ℝ) ^ uniformDeficit (coordinateFiber X s x) * (2 : ℝ) ^ (-194 * k) :=
          mul_le_mul_of_nonneg_left hb.le (by positivity)
        _ = (2 : ℝ) ^ (uniformDeficit (coordinateFiber X s x) - 194 * k) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    · positivity
    · exact le_rfl
  have he := expect_le_expect (s := univ) (fun u _ => hpoint u)
  rw [expect_coordinateMarginal_comp_internal (uniformDensity (coordinateFiber X s x)) R
    (fun v => if v ≤ (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0)] at he
  exact (he.trans hl).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

theorem coordinateDensity_resample_union_internal (X : Finset (ι → Bool)) (P Q x y : ι → Bool) :
    coordinateDensity X Q (resample P x y) =
      coordinateDensity X Q (resample (fun i => P i || Q i) x y) := by
  rw [coordinateDensity_eq_expect, coordinateDensity_eq_expect]
  apply expect_congr rfl
  intro z _
  apply congrArg (fun t => if t ∈ X then (1 : ℝ) else 0)
  funext i
  cases hp : P i <;> cases hq : Q i <;> simp [resample, hp, hq]

theorem fiber_completion_density_union_internal (X : Finset (ι → Bool)) (P Q x : ι → Bool)
    (hx : x ∈ X) {k : ℝ} (hk : 1 ≤ k)
    (hd : uniformDeficit (coordinateFiber X (fun i => P i || Q i) x) ≤ 64 * k)
    (hl : (𝔼 z, if coordinateMarginal
      (uniformDensity (coordinateFiber X (fun i => P i || Q i) x))
      (fun i => P i && !Q i) z ≤ (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-64 * k)) :
    (𝔼 y, if coordinateDensity X Q (resample P x y) < (2 : ℝ) ^ (-194 * k) then
      (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) := by
  let S := fun i => P i || Q i
  let R : {i // S i = true} → Bool := fun i => P i && !Q i
  have hq : (fun i => if h : S i = true then !R ⟨i, h⟩ else false) = Q := by
    funext i
    cases hp : P i <;> cases hq : Q i <;> simp [S, R, hp, hq]
  have ht := fiber_completion_density_internal X S x (coordinateFiber_nonempty S hx) R hk hd hl
  rw [hq] at ht
  simp_rw [coordinateDensity_resample_union_internal X P Q x, resample_eq_completePattern]
  rw [expect_restrict_coordinates S
    (fun u => if coordinateDensity X Q (completePattern S x u) <
      (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0)]
  exact ht

theorem bad_modifications_probability_aux_internal (X : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q r : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / (32768 * k))
    (hjoint : (p + q - p * q) * r = p * (1 - q)) :
    31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if (𝔼 y, if coordinateDensity X Q (resample P x y) <
        (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) then 1 else 0)) := by
  let good (S : ι → Bool) (R : {i // S i = true} → Bool) (x : ι → Bool) : Prop :=
    uniformDeficit (coordinateFiber X S x) ≤ 64 * k ∧
      (𝔼 z, if coordinateMarginal (uniformDensity (coordinateFiber X S x)) R z ≤
        (2 : ℝ) ^ (-128 * k - 2) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-64 * k)
  have htheta : 0 ≤ p + q - p * q ∧ p + q - p * q ≤ 1 := by
    constructor
    · nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hq')]
  have hg : 31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if good (fun i => P i || Q i) (fun i => P i && !Q i) x then
        (1 : ℝ) else 0)) := by
    rw [bernoulliAverage_union_difference_subtype p q r hjoint
      (fun S R => 𝔼 x ∈ X, if good S R x then (1 : ℝ) else 0)]
    have hs (S : ι → Bool) : 31 / 32 ≤ bernoulliAverage r (fun R =>
        𝔼 x ∈ X, if good S R x then (1 : ℝ) else 0) := by
      rw [bernoulliAverage_expect_comm_internal]
      exact coordinateFiber_light_patterns_internal X hX S hk hdef hr hr'
    simpa only [bernoulliAverage_const] using
      bernoulliAverage_mono htheta.1 htheta.2 hs
  refine hg.trans (bernoulliAverage_mono hp hp' fun P =>
    bernoulliAverage_mono hq hq' fun Q => expect_le_expect (s := X) fun x hx => ?_)
  by_cases hg : good (fun i => P i || Q i) (fun i => P i && !Q i) x
  · have hb := fiber_completion_density_union_internal X P Q x hx hk hg.1 hg.2
    simp only [ite_eq_left hg, ite_eq_left hb, le_refl]
  · simp only [ite_eq_right hg]
    split_ifs <;> norm_num

theorem mirror_bad_modifications_probability_internal (X : Finset (ι → Bool)) (hX : X.Nonempty)
    {k p q : ℝ} (hk : 1 ≤ k) (hdef : uniformDeficit X ≤ k) (hp : 0 < p)
    (hq : q = 32768 * k * p) (hq' : q ≤ 1 / 2) :
    31 / 32 ≤ bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      𝔼 x ∈ X, if (𝔼 y, if coordinateDensity X Q (resample P x y) <
        (2 : ℝ) ^ (-194 * k) then (1 : ℝ) else 0) ≤ (2 : ℝ) ^ (-k - 6) then 1 else 0)) := by
  have hqp : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by linarith
  have hpq : p ≤ q := by rw [hq]; nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk)]
  let r := p * (1 - q) / (p + q - p * q)
  have hb := conditionalSamplingRate_bounds hp.le hqp hq1
  have htheta : 0 < p + q - p * q := by
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hq1)]
  have hr : r ≤ 1 / (32768 * k) := by
    refine hb.2.1.trans_eq ?_
    rw [hq]
    field_simp
  exact bad_modifications_probability_aux_internal X hX hk hdef hp.le (hpq.trans hq1) hqp.le hq1
    hb.1 hr (by field_simp)

end Complexity.BooleanAnalysis
