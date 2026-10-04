/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Threshold crossings of Gaussian forms: proofs

Under `gaussPi ι`, the vector `toLp 2 ω` has the standard Gaussian law on
`EuclideanSpace ℝ ι`, and `form a ω` is the inner product with `toLp 2 a`.
Hence `form a` has law `gaussianReal 0 (∑ i, a i ^ 2)`, and two forms with
orthogonal coefficients are jointly Gaussian and uncorrelated, so independent:
their joint law is the product of the two marginals.

The crossing bound conditions on the second form. A real Gaussian density is
at most `1 / √(2πv)`, so an interval of length `2|y|` has probability at most
`2|y| / √(2πv)`; the mean absolute value of `gaussianReal 0 v` is `√(2v/π)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory WithLp Set
open scoped RealInnerProductSpace NNReal ENNReal

/-! ### Real Gaussian estimates -/

/-- The density of `gaussianReal m v` is at most its value at the mean. -/
theorem gaussianPDFReal_le_inv_sqrt (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (√(2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal_def]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- A nondegenerate real Gaussian gives each set at most the peak density times
its Lebesgue measure. -/
theorem gaussianReal_le_mul_volume (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (S : Set ℝ) :
    gaussianReal m v S ≤ ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ * volume S := by
  rw [gaussianReal_apply m hv, ← setLIntegral_const]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_inv_sqrt m v x)

/-- The half-line integral of `x * exp (-b x²)`. -/
theorem integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have h := integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb)
  have h' : ((∫ x in Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) : ℝ) : ℂ) = ((2 * b)⁻¹ : ℝ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact h
  exact_mod_cast h'

/-- The mean absolute value of a centered real Gaussian of variance `v` is
`√(2v/π)`. -/
theorem integral_abs_gaussianReal (v : ℝ≥0) :
    ∫ x, |x| ∂gaussianReal 0 v = √(2 * v / Real.pi) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hv' : (0 : ℝ) < v := by positivity
  set f : ℝ → ℝ := fun y => (√(2 * Real.pi * v))⁻¹ * (y * Real.exp (-(2 * v : ℝ)⁻¹ * y ^ 2))
    with hf
  have hfx : (fun x : ℝ => gaussianPDFReal 0 v x • |x|) = fun x => f |x| := by
    funext x
    simp only [hf, gaussianPDFReal_def, smul_eq_mul, sub_zero, sq_abs]
    ring_nf
  rw [hfx, integral_comp_abs, hf, integral_const_mul,
    integral_Ioi_mul_exp_neg_mul_sq (by positivity)]
  have h2 : 2 * (v : ℝ) / Real.pi = (2 * v) ^ 2 / (2 * Real.pi * v) := by
    field_simp
  rw [h2, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp

/-- For independent centered Gaussians `Y` and `X` of variances `r` and `s > 0`,
the event `|X - c| ≤ |Y|` has probability at most `2 E|Y| / √(2πs)`. -/
theorem prod_gaussianReal_le (r s : ℝ≥0) (hs : s ≠ 0) (c : ℝ) :
    ((gaussianReal 0 r).prod (gaussianReal 0 s)) {p : ℝ × ℝ | |p.2 - c| ≤ |p.1|} ≤
      ENNReal.ofReal ((√(2 * Real.pi * s))⁻¹ * (2 * √(2 * r / Real.pi))) := by
  have hS : MeasurableSet {p : ℝ × ℝ | |p.2 - c| ≤ |p.1|} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [Measure.prod_apply hS]
  have hslice : ∀ y : ℝ, gaussianReal 0 s (Prod.mk y ⁻¹' {p : ℝ × ℝ | |p.2 - c| ≤ |p.1|}) ≤
      ENNReal.ofReal (√(2 * Real.pi * s))⁻¹ * ENNReal.ofReal (2 * |y|) := by
    intro y
    refine (gaussianReal_le_mul_volume 0 hs _).trans ?_
    gcongr
    calc volume (Prod.mk y ⁻¹' {p : ℝ × ℝ | |p.2 - c| ≤ |p.1|})
        ≤ volume (Icc (c - |y|) (c + |y|)) := by
          refine measure_mono fun x hx => ?_
          simp only [mem_preimage, mem_ofPred_eq] at hx
          exact ⟨by linarith [(abs_le.1 hx).1], by linarith [(abs_le.1 hx).2]⟩
      _ = ENNReal.ofReal (2 * |y|) := by rw [Real.volume_Icc]; ring_nf
  calc ∫⁻ y, gaussianReal 0 s (Prod.mk y ⁻¹' {p : ℝ × ℝ | |p.2 - c| ≤ |p.1|}) ∂gaussianReal 0 r
      ≤ ∫⁻ y, ENNReal.ofReal (√(2 * Real.pi * s))⁻¹ * ENNReal.ofReal (2 * |y|)
          ∂gaussianReal 0 r :=
        lintegral_mono hslice
    _ = ENNReal.ofReal (√(2 * Real.pi * s))⁻¹ *
          ∫⁻ y, ENNReal.ofReal (2 * |y|) ∂gaussianReal 0 r :=
        lintegral_const_mul _ (by fun_prop)
    _ = ENNReal.ofReal (√(2 * Real.pi * s))⁻¹ * ENNReal.ofReal (2 * √(2 * r / Real.pi)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul, integral_abs_gaussianReal]
        · exact (IsGaussian.integrable_id.abs).const_mul 2
        · exact ae_of_all _ fun y => by positivity
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- The constant in the crossing bound. -/
theorem crossing_const_eq {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    (√(2 * Real.pi * s))⁻¹ * (2 * √(2 * r / Real.pi)) = 2 / Real.pi * (√r / √s) := by
  have hπ := Real.pi_pos
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity),
    Real.sqrt_mul (by positivity)]
  have h2 : 0 < √2 := by positivity
  have h3 : 0 < √Real.pi := Real.sqrt_pos.2 hπ
  have h4 : 0 < √s := Real.sqrt_pos.2 hs
  field_simp
  rw [Real.sq_sqrt hπ.le, mul_comm]

/-! ### Laws of Gaussian forms -/

section Forms

variable {ι : Type} [Fintype ι]

/-- A form is the inner product of the coefficient and sample vectors. -/
theorem form_eq_inner (a ω : ι → ℝ) :
    form a ω = innerSL ℝ (toLp 2 a : EuclideanSpace ℝ ι) (toLp 2 ω) := by
  simp [form, PiLp.inner_apply, mul_comm]

theorem measurable_form (a : ι → ℝ) : Measurable (form a) := by
  unfold form; fun_prop

/-- Under the standard Gaussian, the inner product with `u` has law
`gaussianReal 0 ‖u‖²`. -/
theorem map_innerSL_stdGaussian (u : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (innerSL ℝ u) =
      gaussianReal 0 (‖u‖ ^ 2).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm]

/-- Under the standard Gaussian, inner products have covariance `⟪u, v⟫`. -/
theorem cov_innerSL_stdGaussian (u v : EuclideanSpace ℝ ι) :
    cov[innerSL ℝ u, innerSL ℝ v; stdGaussian (EuclideanSpace ℝ ι)] = ⟪u, v⟫ := by
  have h := covarianceBilin_apply_eq_cov (μ := stdGaussian (EuclideanSpace ℝ ι))
    IsGaussian.memLp_two_id u v
  rw [covarianceBilin_stdGaussian, innerSL_apply_apply ℝ] at h
  exact h.symm

/-- Inner products with orthogonal vectors are independent under the standard
Gaussian, so their joint law is the product of their marginals. -/
theorem map_pair_stdGaussian (u v : EuclideanSpace ℝ ι) (huv : ⟪u, v⟫ = 0) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => (innerSL ℝ u x, innerSL ℝ v x)) =
      (gaussianReal 0 (‖u‖ ^ 2).toNNReal).prod (gaussianReal 0 (‖v‖ ^ 2).toNNReal) := by
  have hlaw : HasGaussianLaw (fun x => (innerSL ℝ u x, innerSL ℝ v x))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    IsGaussian.hasGaussianLaw_id.map_fun ((innerSL ℝ u).prod (innerSL ℝ v))
  have hind := hlaw.indepFun_of_covariance_eq_zero (by rw [cov_innerSL_stdGaussian, huv])
  rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1 hind,
    map_innerSL_stdGaussian, map_innerSL_stdGaussian]

/-- The law of a Gaussian form. -/
theorem gaussPi_map_form (a : ι → ℝ) :
    (gaussPi ι).map (form a) = gaussianReal 0 (∑ i, a i ^ 2).toNNReal := by
  have h : form a = innerSL ℝ (toLp 2 a : EuclideanSpace ℝ ι) ∘ toLp 2 := by
    funext ω; exact form_eq_inner a ω
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian,
    map_innerSL_stdGaussian, EuclideanSpace.real_norm_sq_eq]

/-- Two Gaussian forms with orthogonal coefficients are independent: their joint
law is the product of their marginal laws. -/
theorem gaussPi_map_form_pair (a b : ι → ℝ) (hab : ∑ i, a i * b i = 0) :
    (gaussPi ι).map (fun ω => (form a ω, form b ω)) =
      (gaussianReal 0 (∑ i, a i ^ 2).toNNReal).prod
        (gaussianReal 0 (∑ i, b i ^ 2).toNNReal) := by
  have h : (fun ω => (form a ω, form b ω)) =
      (fun x => (innerSL ℝ (toLp 2 a : EuclideanSpace ℝ ι) x,
        innerSL ℝ (toLp 2 b : EuclideanSpace ℝ ι) x)) ∘ toLp 2 := by
    funext ω; simp only [Function.comp_apply, form_eq_inner]
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian,
    map_pair_stdGaussian, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simpa [PiLp.inner_apply, mul_comm] using hab

/-! ### The three bounds -/

theorem gaussPi_between_le (α β : ι → ℝ)
    (hnorm : ∑ i, α i ^ 2 = ∑ i, β i ^ 2) (hsum : 0 < ∑ i, (α i + β i) ^ 2) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      2 / Real.pi * (Real.sqrt (∑ i, (β i - α i) ^ 2) / Real.sqrt (∑ i, (α i + β i) ^ 2)) := by
  set a : ι → ℝ := fun i => β i - α i with ha
  set b : ι → ℝ := fun i => α i + β i with hb
  have hab : ∑ i, a i * b i = 0 := by
    have h : ∀ i, a i * b i = β i ^ 2 - α i ^ 2 := fun i => by simp only [ha, hb]; ring
    simp_rw [h, Finset.sum_sub_distrib, hnorm, sub_self]
  set S : Set (ℝ × ℝ) := {p | |p.2 - 2 * t| ≤ |p.1|} with hS
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) (by fun_prop)
  have hsub : {ω | Between t (form α ω) (form β ω)} ⊆
      (fun ω => (form a ω, form b ω)) ⁻¹' S := by
    intro ω hω
    have hU : form b ω = form α ω + form β ω := by
      simp only [form, hb, add_mul, Finset.sum_add_distrib]
    have hV : form a ω = form β ω - form α ω := by
      simp only [form, ha, sub_mul, Finset.sum_sub_distrib]
    simp only [mem_preimage, hS, mem_ofPred_eq, hU, hV]
    refine abs_le.2 ⟨?_, ?_⟩ <;> rcases hω with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases abs_cases (form β ω - form α ω) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> linarith
  have hpair : Measurable fun ω => (form a ω, form b ω) :=
    (measurable_form a).prodMk (measurable_form b)
  have hs0 : (∑ i, b i ^ 2).toNNReal ≠ 0 := by simpa [hb] using hsum
  have hnn : ∀ c : ι → ℝ, 0 ≤ ∑ i, c i ^ 2 := fun c => Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (gaussPi ι).real {ω | Between t (form α ω) (form β ω)}
      ≤ (gaussPi ι).real ((fun ω => (form a ω, form b ω)) ⁻¹' S) := measureReal_mono hsub
    _ = ((gaussianReal 0 (∑ i, a i ^ 2).toNNReal).prod
          (gaussianReal 0 (∑ i, b i ^ 2).toNNReal)).real S := by
        rw [← map_measureReal_apply hpair hSm, gaussPi_map_form_pair a b hab]
    _ ≤ _ := by
        refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
        refine (prod_gaussianReal_le _ _ hs0 (2 * t)).trans_eq ?_
        rw [Real.coe_toNNReal _ (hnn a), Real.coe_toNNReal _ (hnn b),
          crossing_const_eq (hnn a) (by simpa [hb] using hsum)]

theorem gaussPi_window_le (α : ι → ℝ) (hα : ∑ i, α i ^ 2 = 1)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussPi ι).real {ω | s ≤ form α ω ∧ form α ω < s + δ} ≤ δ / Real.sqrt (2 * Real.pi) := by
  have hset : {ω | s ≤ form α ω ∧ form α ω < s + δ} = form α ⁻¹' Ico s (s + δ) := rfl
  rw [hset, ← map_measureReal_apply (measurable_form α) measurableSet_Ico, gaussPi_map_form, hα,
    Real.toNNReal_one]
  have h := gaussianReal_le_mul_volume 0 one_ne_zero (Ico s (s + δ))
  rw [Real.volume_Ico, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity)] at h
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) h).trans_eq ?_
  simp [div_eq_inv_mul]

theorem gaussPi_tail_le (α : ι → ℝ) (hα : ∑ i, α i ^ 2 = 1)
    {T : ℝ} (hT : 0 < T) :
    (gaussPi ι).real {ω | T ≤ |form α ω|} ≤ 1 / T ^ 2 := by
  have hset : {ω | T ≤ |form α ω|} = form α ⁻¹' {x | T ≤ |x|} := rfl
  rw [hset, ← map_measureReal_apply (measurable_form α) (measurableSet_le (by fun_prop)
    (by fun_prop)), gaussPi_map_form, hα, Real.toNNReal_one]
  have h := meas_ge_le_variance_div_sq (μ := gaussianReal 0 1) (memLp_id_gaussianReal 2) hT
  simp only [variance_id_gaussianReal] at h
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  simpa using h

end Forms

end Algebraic.Cutwidth.Gaussian.Internal
