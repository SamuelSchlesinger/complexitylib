/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Internal
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Sheppard's crossing bound: proofs

* **Planar angle law.** In polar coordinates `(r, θ)` the product of two standard
  Gaussians has density `exp (-r²/2) / (2π)`, and for `r > 0` the event `|x| ≤ k |y|`
  depends on `θ` alone: it holds on the two arcs of `(-π, π)` of half-width `arctan k`
  centered at `±π/2`. The radial factor `r exp (-r²/2)` integrates to one, so the event
  has probability `4 arctan k / (2π)`.
* **Anderson's inequality on the line.** For a centered Gaussian, `[c - w, c + w]` has at
  most the mass of `[-w, w]`. By symmetry take `c ≥ 0`; the intervals share `[c - w, w]`,
  and translation by `2w` carries `[-w, c - w]` onto `[w, c + w]` without increasing the
  density.
* **Sheppard's bound.** The forms `U = form (α + β)` and `V = form (β - α)` are independent
  centered Gaussians, and a crossing forces `|U - 2t| ≤ |V|`. Conditioning on `V`,
  Anderson's inequality removes the shift `2t`. Rescaling `U` and `V` to standard
  Gaussians turns `|U| ≤ |V|` into the planar angle event with
  `k = ‖β - α‖ / ‖α + β‖`.
* **Half-angle identity.** `y = tanHalf x` has `cos (2 arctan y) = (1 - y²) / (1 + y²) = x`
  and `0 ≤ 2 arctan y < π`, so `2 arctan y = arccos x`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal ENNReal

/-! ### The planar angle law -/

/-- The standard planar Gaussian density in polar coordinates. -/
theorem gaussianPDFReal_mul_polar (r θ : ℝ) :
    gaussianPDFReal 0 1 (r * cos θ) * gaussianPDFReal 0 1 (r * sin θ) =
      (2 * π)⁻¹ * exp (-2⁻¹ * r ^ 2) := by
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
  rw [mul_mul_mul_comm, ← mul_inv, Real.mul_self_sqrt (by positivity), ← Real.exp_add]
  congr 2
  linear_combination (-2⁻¹ * r ^ 2) * sin_sq_add_cos_sq θ

/-- The angles with `|cos θ| ≤ k |sin θ|` are those with `|cos θ| ≤ sin (arctan k)`. -/
theorem abs_cos_le_mul_abs_sin_iff {k : ℝ} (hk : 0 ≤ k) (θ : ℝ) :
    |cos θ| ≤ k * |sin θ| ↔ |cos θ| ≤ sin (arctan k) := by
  have hs : 0 ≤ sin (arctan k) := sin_arctan_nonneg.2 hk
  rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), ← sq_le_sq₀ (abs_nonneg _) hs, mul_pow,
    sq_abs, sq_abs, sin_arctan, div_pow, sq_sqrt (by positivity), sin_sq,
    le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The angles in `(-π, π)` with `|cos θ| ≤ k |sin θ|` form two arcs centered at `±π/2`. -/
theorem angle_set_eq {k : ℝ} (hk : 0 ≤ k) :
    {θ : ℝ | |cos θ| ≤ k * |sin θ|} ∩ Ioo (-π) π =
      Icc (π / 2 - arctan k) (π / 2 + arctan k) ∪
        Icc (-(π / 2 + arctan k)) (-(π / 2 - arctan k)) := by
  set a := arctan k with ha
  have ha0 : 0 ≤ a := arctan_nonneg.2 hk
  have ha1 : a < π / 2 := arctan_lt_pi_div_two k
  have hmem : ∀ ψ ∈ Icc (0 : ℝ) π,
      |cos ψ| ≤ sin a ↔ π / 2 - a ≤ ψ ∧ ψ ≤ π / 2 + a := by
    intro ψ hψ
    have h1 : π / 2 - a ∈ Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
    have h2 : π / 2 + a ∈ Icc (0 : ℝ) π := ⟨by linarith, by linarith⟩
    have e1 : -sin a = cos (π / 2 + a) := by rw [add_comm, cos_add_pi_div_two]
    rw [abs_le, e1, ← cos_pi_div_two_sub, strictAntiOn_cos.le_iff_ge h2 hψ,
      strictAntiOn_cos.le_iff_ge hψ h1, and_comm]
  ext θ
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioo, mem_union, mem_Icc]
  rw [abs_cos_le_mul_abs_sin_iff hk, ← ha]
  constructor
  · rintro ⟨h, h1, h2⟩
    rw [← cos_abs] at h
    have := (hmem |θ| ⟨abs_nonneg _, abs_le.2 ⟨by linarith, by linarith⟩⟩).1 h
    rcases abs_cases θ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at this
    · exact Or.inl this
    · exact Or.inr ⟨by linarith, by linarith⟩
  · intro h
    have hθ : π / 2 - a ≤ |θ| ∧ |θ| ≤ π / 2 + a := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩
      · rw [abs_of_neg (by linarith)]; exact ⟨by linarith, by linarith⟩
    have hb := abs_lt.1 (show |θ| < π by linarith)
    refine ⟨?_, by linarith, by linarith⟩
    rw [← cos_abs]
    exact (hmem |θ| ⟨abs_nonneg _, by linarith⟩).2 hθ

/-- The angles in `(-π, π)` with `|cos θ| ≤ k |sin θ|` have total length `4 arctan k`. -/
theorem volume_angle_set {k : ℝ} (hk : 0 ≤ k) :
    volume ({θ : ℝ | |cos θ| ≤ k * |sin θ|} ∩ Ioo (-π) π) = ENNReal.ofReal (4 * arctan k) := by
  have ha0 : 0 ≤ arctan k := arctan_nonneg.2 hk
  have ha1 : arctan k < π / 2 := arctan_lt_pi_div_two k
  rw [angle_set_eq hk, measure_union _ measurableSet_Icc, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  · congr 1; ring
  · refine Set.disjoint_left.2 fun θ h1 h2 => ?_
    linarith [h1.1, h2.2]

/-- The radial factor of the planar Gaussian integrates to one. -/
theorem lintegral_radial :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((2 * π)⁻¹ * (r * exp (-2⁻¹ * r ^ 2))) =
      ENNReal.ofReal (2 * π)⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul,
    integral_Ioi_mul_exp_neg_mul_sq (by norm_num)]
  · norm_num
  · exact ((integrable_mul_exp_neg_mul_sq (by norm_num)).const_mul _).integrableOn
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => ?_)
    have : 0 < r := hr
    positivity

/-- **Planar angle law** for the product of two standard Gaussians. -/
theorem prod_gaussianReal_abs_le (k : ℝ) (hk : 0 ≤ k) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {p : ℝ × ℝ | |p.1| ≤ k * |p.2|} =
      ENNReal.ofReal (2 / π * arctan k) := by
  set A : Set (ℝ × ℝ) := {p | |p.1| ≤ k * |p.2|} with hA
  have hAm : MeasurableSet A := measurableSet_le (by fun_prop) (by fun_prop)
  set B : Set ℝ := {θ | |cos θ| ≤ k * |sin θ|} with hB
  have hBm : MeasurableSet B := measurableSet_le (by fun_prop) (by fun_prop)
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    withDensity_apply _ hAm, ← Measure.volume_eq_prod, ← lintegral_indicator hAm,
    ← lintegral_comp_polarCoord_symm]
  have hint : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • A.indicator
          (fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) (polarCoord.symm p) =
        ENNReal.ofReal ((2 * π)⁻¹ * (p.1 * exp (-2⁻¹ * p.1 ^ 2))) * B.indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    have hiff : (r * cos θ, r * sin θ) ∈ A ↔ θ ∈ B := by
      simp only [hA, hB, mem_ofPred_eq, abs_mul, abs_of_pos hr]
      rw [mul_left_comm, mul_le_mul_iff_right₀ hr]
    simp only [polarCoord_symm_apply, smul_eq_mul]
    by_cases hθ : θ ∈ B
    · rw [indicator_of_mem (hiff.2 hθ), indicator_of_mem hθ, Pi.one_apply, mul_one,
        gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        gaussianPDFReal_mul_polar, ← ENNReal.ofReal_mul hr.le]
      congr 1; ring
    · rw [indicator_of_notMem (mt hiff.1 hθ), indicator_of_notMem hθ, mul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hint,
    polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r => ENNReal.ofReal ((2 * π)⁻¹ * (r * exp (-2⁻¹ * r ^ 2))))
      (g := B.indicator 1) (by fun_prop) ((measurable_one.indicator hBm).aemeasurable),
    lintegral_radial,
    lintegral_indicator_one hBm, Measure.restrict_apply hBm, volume_angle_set hk,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- **Planar angle law** for `gaussPi (Fin 2)`. -/
theorem gaussPi_abs_le_mul_abs (k : ℝ) (hk : 0 ≤ k) :
    (gaussPi (Fin 2)).real {ω | |ω 0| ≤ k * |ω 1|} = 2 / π * arctan k := by
  have hA : MeasurableSet {p : ℝ × ℝ | |p.1| ≤ k * |p.2|} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hset : {ω : Fin 2 → ℝ | |ω 0| ≤ k * |ω 1|} =
      MeasurableEquiv.finTwoArrow ⁻¹' {p : ℝ × ℝ | |p.1| ≤ k * |p.2|} := rfl
  rw [measureReal_def, hset,
    (measurePreserving_finTwoArrow (gaussianReal 0 1)).measure_preimage hA.nullMeasurableSet,
    prod_gaussianReal_abs_le k hk, ENNReal.toReal_ofReal (by positivity [arctan_nonneg.2 hk])]

/-! ### Symmetric intervals carry the most mass -/

/-- If translating by `2w` does not increase `f` to the right of `-w`, then the
interval of radius `w` around `c ≥ 0` carries at most the mass of the centered one. -/
theorem intervalIntegral_shift_le {f : ℝ → ℝ} (hf : Continuous f) {c w : ℝ} (hc : 0 ≤ c)
    (hmono : ∀ x, -w ≤ x → f (x + 2 * w) ≤ f x) :
    ∫ x in (c - w)..(c + w), f x ≤ ∫ x in (-w)..w, f x := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (c - w) w) (hf.intervalIntegrable w (c + w))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-w) (c - w)) (hf.intervalIntegrable (c - w) w)
  have h3 : ∫ x in w..(c + w), f x = ∫ x in (-w)..(c - w), f (x + 2 * w) := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  have h4 : ∫ x in (-w)..(c - w), f (x + 2 * w) ≤ ∫ x in (-w)..(c - w), f x :=
    intervalIntegral.integral_mono_on (by linarith)
      ((hf.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)
      fun x hx => hmono x hx.1
  linarith

/-- The centered Gaussian density is even. -/
theorem gaussianPDFReal_neg (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v (-x) = gaussianPDFReal 0 v x := by
  simp [gaussianPDFReal_def]

/-- The centered Gaussian density decreases under the translation by `2w` to the right
of `-w`. -/
theorem gaussianPDFReal_add_two_mul_le (v : ℝ≥0) {w x : ℝ} (hw : 0 ≤ w) (hx : -w ≤ x) :
    gaussianPDFReal 0 v (x + 2 * w) ≤ gaussianPDFReal 0 v x := by
  simp only [gaussianPDFReal_def, sub_zero]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- **One-dimensional Anderson inequality.** For a centered Gaussian, an interval of
radius `w` carries the most mass when it is centered at the mean. -/
theorem gaussianReal_Icc_le (v : ℝ≥0) (c w : ℝ) :
    gaussianReal 0 v (Icc (c - w) (c + w)) ≤ gaussianReal 0 v (Icc (-w) w) := by
  rcases lt_or_ge w 0 with hw | hw
  · rw [Icc_eq_empty (by linarith), measure_empty]
    exact bot_le
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var, Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ Icc (-w) w from
      ⟨by linarith, hw⟩)]
    exact prob_le_one
  rw [gaussianReal_apply_eq_integral _ hv, gaussianReal_apply_eq_integral _ hv,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcont : Continuous (gaussianPDFReal 0 v) := by
    rw [gaussianPDFReal_def]; fun_prop
  have hmono : ∀ x, -w ≤ x → gaussianPDFReal 0 v (x + 2 * w) ≤ gaussianPDFReal 0 v x :=
    fun x hx => gaussianPDFReal_add_two_mul_le v hw hx
  rcases le_total 0 c with hc | hc
  · exact intervalIntegral_shift_le hcont hc hmono
  · have hrefl : ∫ x in (c - w)..(c + w), gaussianPDFReal 0 v x =
        ∫ x in (-c - w)..(-c + w), gaussianPDFReal 0 v x := by
      calc ∫ x in (c - w)..(c + w), gaussianPDFReal 0 v x
          = ∫ x in (c - w)..(c + w), gaussianPDFReal 0 v (-x) := by
            simp only [gaussianPDFReal_neg]
        _ = _ := by
            rw [intervalIntegral.integral_comp_neg]
            congr 1 <;> ring
    rw [hrefl]
    exact intervalIntegral_shift_le hcont (by linarith) hmono

/-- Anderson's inequality for the event `|X - c| ≤ |Y|` with `X`, `Y` independent
and `X` centered Gaussian. -/
theorem prod_gaussianReal_sub_le (s r : ℝ≥0) (c : ℝ) :
    ((gaussianReal 0 s).prod (gaussianReal 0 r)) {p : ℝ × ℝ | |p.1 - c| ≤ |p.2|} ≤
      ((gaussianReal 0 s).prod (gaussianReal 0 r)) {p : ℝ × ℝ | |p.1| ≤ |p.2|} := by
  rw [Measure.prod_apply_symm (measurableSet_le (by fun_prop) (by fun_prop)),
    Measure.prod_apply_symm (measurableSet_le (by fun_prop) (by fun_prop))]
  refine lintegral_mono fun y => ?_
  have e1 : (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | |p.1 - c| ≤ |p.2|} = Icc (c - |y|) (c + |y|) := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have e2 : (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | |p.1| ≤ |p.2|} = Icc (-|y|) |y| := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_Icc]
    exact abs_le
  rw [e1, e2]
  exact gaussianReal_Icc_le s c |y|

/-- `gaussianReal 0 s` is the image of the standard Gaussian under `x ↦ √s x`. -/
theorem gaussianReal_map_sqrt_mul (s : ℝ≥0) :
    (gaussianReal 0 1).map (fun x => √(s : ℝ) * x) = gaussianReal 0 s := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp

/-- **Planar angle law** for two independent centered Gaussians of variances `s > 0`
and `r`. -/
theorem prod_gaussianReal_abs_le_abs (s r : ℝ≥0) (hs : s ≠ 0) :
    ((gaussianReal 0 s).prod (gaussianReal 0 r)) {p : ℝ × ℝ | |p.1| ≤ |p.2|} =
      ENNReal.ofReal (2 / π * arctan (√(r : ℝ) / √(s : ℝ))) := by
  have hs' : 0 < √(s : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [← gaussianReal_map_sqrt_mul s, ← gaussianReal_map_sqrt_mul r,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))]
  have hpre : Prod.map (fun x => √(s : ℝ) * x) (fun x => √(r : ℝ) * x) ⁻¹'
      {p : ℝ × ℝ | |p.1| ≤ |p.2|} = {p : ℝ × ℝ | |p.1| ≤ √(r : ℝ) / √(s : ℝ) * |p.2|} := by
    ext p
    simp only [mem_preimage, Prod.map_fst, Prod.map_snd, mem_ofPred_eq, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hs', mul_comm]
  rw [hpre, prod_gaussianReal_abs_le _ (by positivity)]

/-! ### Sheppard's bound -/

/-- A threshold separating two values lies within half their gap of their midpoint. -/
theorem abs_add_sub_two_mul_le_of_between {t x y : ℝ} (h : Between t x y) :
    |x + y - 2 * t| ≤ |y - x| := by
  refine abs_le.2 ⟨?_, ?_⟩ <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (y - x) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> linarith

/-- **Sheppard's bound** for coefficient vectors of equal norm with nonzero sum. -/
theorem gaussPi_between_le_arctan {ι : Type} [Fintype ι] (α β : ι → ℝ)
    (hnorm : ∑ i, α i ^ 2 = ∑ i, β i ^ 2) (hsum : 0 < ∑ i, (α i + β i) ^ 2) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      2 / π * arctan (√(∑ i, (β i - α i) ^ 2) / √(∑ i, (α i + β i) ^ 2)) := by
  set a : ι → ℝ := fun i => β i - α i with ha
  set b : ι → ℝ := fun i => α i + β i with hb
  have hba : ∑ i, b i * a i = 0 := by
    have h : ∀ i, b i * a i = β i ^ 2 - α i ^ 2 := fun i => by simp only [ha, hb]; ring
    simp_rw [h, Finset.sum_sub_distrib, hnorm, sub_self]
  set S : Set (ℝ × ℝ) := {p | |p.1 - 2 * t| ≤ |p.2|} with hS
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) (by fun_prop)
  have hsub : {ω | Between t (form α ω) (form β ω)} ⊆
      (fun ω => (form b ω, form a ω)) ⁻¹' S := by
    intro ω hω
    have hU : form b ω = form α ω + form β ω := by
      simp only [form, hb, add_mul, Finset.sum_add_distrib]
    have hV : form a ω = form β ω - form α ω := by
      simp only [form, ha, sub_mul, Finset.sum_sub_distrib]
    simpa only [mem_preimage, hS, mem_ofPred_eq, hU, hV] using
      abs_add_sub_two_mul_le_of_between hω
  have hpair : Measurable fun ω => (form b ω, form a ω) :=
    (measurable_form b).prodMk (measurable_form a)
  have hs0 : (∑ i, b i ^ 2).toNNReal ≠ 0 := by simpa [hb] using hsum
  have hnn : ∀ c : ι → ℝ, 0 ≤ ∑ i, c i ^ 2 := fun c => Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (gaussPi ι).real {ω | Between t (form α ω) (form β ω)}
      ≤ (gaussPi ι).real ((fun ω => (form b ω, form a ω)) ⁻¹' S) := measureReal_mono hsub
    _ = ((gaussianReal 0 (∑ i, b i ^ 2).toNNReal).prod
          (gaussianReal 0 (∑ i, a i ^ 2).toNNReal)).real S := by
        rw [← map_measureReal_apply hpair hSm, gaussPi_map_form_pair b a hba]
    _ ≤ ((gaussianReal 0 (∑ i, b i ^ 2).toNNReal).prod
          (gaussianReal 0 (∑ i, a i ^ 2).toNNReal)).real {p : ℝ × ℝ | |p.1| ≤ |p.2|} :=
        ENNReal.toReal_mono (measure_ne_top _ _) (prod_gaussianReal_sub_le _ _ _)
    _ = _ := by
        rw [measureReal_def, prod_gaussianReal_abs_le_abs _ _ hs0,
          ENNReal.toReal_ofReal (by positivity [arctan_nonneg.2 (by positivity :
            0 ≤ √(((∑ i, a i ^ 2).toNNReal : ℝ)) / √(((∑ i, b i ^ 2).toNNReal : ℝ)))]),
          Real.coe_toNNReal _ (hnn a), Real.coe_toNNReal _ (hnn b)]

/-- `2 arctan (tanHalf x) = arccos x`. -/
theorem two_mul_arctan_tanHalf {x : ℝ} (hx : -1 < x) (hx1 : x ≤ 1) :
    2 * arctan (tanHalf x) = arccos x := by
  set y := tanHalf x with hy
  have hy0 : 0 ≤ y := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hy2 : y ^ 2 = (1 - x) / (1 + x) := by
    rw [hy, tanHalf, div_pow, sq_sqrt (by linarith), sq_sqrt (by linarith)]
  have hcos : cos (2 * arctan y) = x := by
    have h1 : (0 : ℝ) < 1 + x := by linarith
    rw [cos_two_mul, cos_sq_arctan, hy2]
    field_simp
    ring
  rw [← hcos, arccos_cos (by positivity [arctan_nonneg.2 hy0])
    (by linarith [arctan_lt_pi_div_two y])]

/-- **Sheppard's bound** for unit forms. -/
theorem gaussPi_between_le_arccos {ι : Type} [Fintype ι] {α β : ι → ℝ}
    (hα : ∑ i, α i ^ 2 = 1) (hβ : ∑ i, β i ^ 2 = 1) (hx : -1 < ∑ i, α i * β i) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      arccos (∑ i, α i * β i) / π := by
  set x := ∑ i, α i * β i with hxdef
  have hplus : ∑ i, (α i + β i) ^ 2 = 2 * (1 + x) := by
    have h : ∀ i, (α i + β i) ^ 2 = α i ^ 2 + β i ^ 2 + 2 * (α i * β i) := fun i => by ring
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hα, hβ, hxdef]
    ring
  have hminus : ∑ i, (β i - α i) ^ 2 = 2 * (1 - x) := by
    have h : ∀ i, (β i - α i) ^ 2 = α i ^ 2 + β i ^ 2 - 2 * (α i * β i) := fun i => by ring
    simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hα, hβ,
      hxdef]
    ring
  have hx1 : x ≤ 1 := by
    have : 0 ≤ ∑ i, (β i - α i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  refine (gaussPi_between_le_arctan α β (by rw [hα, hβ]) (by rw [hplus]; linarith) t).trans_eq ?_
  rw [hplus, hminus, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num),
    mul_div_mul_left _ _ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne',
    show √(1 - x) / √(1 + x) = tanHalf x from rfl, ← two_mul_arctan_tanHalf hx hx1]
  ring

end Algebraic.Cutwidth.Gaussian.Internal
