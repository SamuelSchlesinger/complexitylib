/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact.Internal
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Threshold decay of Gaussian crossings: proofs

* **Angular window.** Write a point of the plane as `(R cos ψ, R sin ψ)` with `R > 0` and
  `ψ ∈ (-π, π)`, and put `θ = |ψ|`. Then `cos ψ = cos θ` and `|sin ψ| = sin θ`, so for
  `φ ≥ 0` the event `|cos φ x - c| ≤ sin φ |y|` reads
  `R cos (θ + φ) ≤ c ≤ R cos (θ - φ)`. Hence `|c| ≤ R`, and with `m = arccos (c / R)`,
  monotonicity of `arccos` gives `|θ - m| ≤ φ`. So at each radius the event occupies at
  most two arcs of length `2φ`, and none below radius `|c|`.
* **Radial tail.** `R exp (-R²/2)` has antiderivative `-exp (-R²/2)`, so its integral over
  `R > a` is `exp (-a²/2)`.
* **Decay of the angle law.** In polar coordinates the standard planar Gaussian has density
  `exp (-R²/2) / (2π)`. Bounding the angular slice by `4φ` above radius `|c|` and
  integrating the radial tail gives `(2/π) φ exp (-c²/2)`.
* **Crossings.** As in Sheppard's bound, `U = form (α + β)` and `V = form (β - α)` are
  independent and a crossing forces `|U - 2t| ≤ |V|`. Rescaling to standard Gaussians puts
  this event in the above form with `tan φ = ‖β - α‖ / ‖α + β‖` and threshold
  `2t / √(‖α + β‖² + ‖β - α‖²)`; no Anderson step is needed.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

open MeasureTheory ProbabilityTheory Set Real Filter Topology
open scoped NNReal ENNReal

/-! ### The angular window -/

/-- On `[-π, π]`, `|sin ψ| = sin |ψ|`. -/
theorem abs_sin_eq_sin_abs {ψ : ℝ} (h : |ψ| ≤ π) : |sin ψ| = sin |ψ| := by
  have hs : 0 ≤ sin |ψ| := sin_nonneg_of_nonneg_of_le_pi (abs_nonneg ψ) h
  rcases abs_cases ψ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hs ⊢
  · exact abs_of_nonneg hs
  · rw [sin_neg] at hs ⊢
    exact abs_of_nonpos (by linarith)

/-- If `cos (θ + φ) ≤ y ≤ cos (θ - φ)` with `θ ∈ [0, π]` and `φ ≥ 0`, then `θ` lies within
`φ` of `arccos y`. -/
theorem abs_sub_arccos_le {θ φ y : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) (hφ : 0 ≤ φ)
    (h1 : cos (θ + φ) ≤ y) (h2 : y ≤ cos (θ - φ)) : |θ - arccos y| ≤ φ := by
  rw [abs_le]
  constructor
  · rcases le_or_gt (θ + φ) π with h | h
    · have := antitone_arccos h1
      rw [arccos_cos (by linarith) h] at this
      linarith
    · linarith [arccos_le_pi y]
  · rcases le_or_gt (θ - φ) 0 with h | h
    · linarith [arccos_nonneg y]
    · have := antitone_arccos h2
      rw [arccos_cos h.le (by linarith)] at this
      linarith

/-- At radius `R > 0` and angle `ψ ∈ [-π, π]`, the event `|cos φ x - c| ≤ sin φ |y|` forces
`|c| ≤ R` and puts `|ψ|` within `φ` of `arccos (c / R)`. -/
theorem polar_event {φ c R ψ : ℝ} (hφ : 0 ≤ φ) (hR : 0 < R) (hψ : |ψ| ≤ π)
    (h : |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|) :
    |c| ≤ R ∧ |(|ψ|) - arccos (c / R)| ≤ φ := by
  rw [abs_mul, abs_of_pos hR, abs_sin_eq_sin_abs hψ, ← cos_abs ψ] at h
  have h' := abs_le.1 h
  have hlo : R * cos (|ψ| + φ) ≤ c := by rw [cos_add]; nlinarith [h'.2]
  have hhi : c ≤ R * cos (|ψ| - φ) := by rw [cos_sub]; nlinarith [h'.1]
  have hc1 : c / R ≤ cos (|ψ| - φ) := by rw [div_le_iff₀ hR]; linarith
  have hc2 : cos (|ψ| + φ) ≤ c / R := by rw [le_div_iff₀ hR]; linarith
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_sub_arccos_le (abs_nonneg ψ) hψ hφ hc2 hc1⟩
  · nlinarith [mul_le_mul_of_nonneg_left (neg_one_le_cos (|ψ| + φ)) hR.le]
  · nlinarith [mul_le_mul_of_nonneg_left (cos_le_one (|ψ| - φ)) hR.le]

/-- At radius `R > 0`, the angles in `(-π, π)` of the event `|cos φ x - c| ≤ sin φ |y|` have
total length at most `4φ`, and there are none unless `|c| ≤ R`. -/
theorem volume_polar_event_le {φ c R : ℝ} (hφ : 0 ≤ φ) (hR : 0 < R) :
    volume ({ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|} ∩ Ioo (-π) π) ≤
      (Ici |c|).indicator (fun _ => ENNReal.ofReal (4 * φ)) R := by
  set m := arccos (c / R)
  by_cases hc : |c| ≤ R
  · rw [indicator_of_mem (show R ∈ Ici |c| from hc)]
    calc volume ({ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|} ∩ Ioo (-π) π)
        ≤ volume (Icc (m - φ) (m + φ) ∪ Icc (-(m + φ)) (-(m - φ))) := by
          refine measure_mono fun ψ ⟨h, h1, h2⟩ => ?_
          have := abs_le.1 (polar_event hφ hR (abs_le.2 ⟨h1.le, h2.le⟩) h).2
          rcases abs_cases ψ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at this
          · exact Or.inl ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨by linarith, by linarith⟩
      _ ≤ volume (Icc (m - φ) (m + φ)) + volume (Icc (-(m + φ)) (-(m - φ))) :=
          measure_union_le _ _
      _ = ENNReal.ofReal (4 * φ) := by
          rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
  · rw [indicator_of_notMem (show R ∉ Ici |c| from hc)]
    have hempty : {ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|} ∩ Ioo (-π) π = ∅ :=
      eq_empty_of_forall_notMem fun ψ ⟨h, h1, h2⟩ =>
        hc (polar_event hφ hR (abs_le.2 ⟨h1.le, h2.le⟩) h).1
    rw [hempty, measure_empty]

/-! ### The radial tail -/

/-- The radial tail `∫_{R > a} R exp (-R²/2) dR = exp (-a²/2)`. -/
theorem integral_Ioi_mul_exp_neg_half_sq (a : ℝ) :
    ∫ R in Ioi a, R * exp (-2⁻¹ * R ^ 2) = exp (-2⁻¹ * a ^ 2) := by
  have hderiv : ∀ x ∈ Ici a,
      HasDerivAt (fun R => -exp (-2⁻¹ * R ^ 2)) (x * exp (-2⁻¹ * x ^ 2)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).const_mul (-2⁻¹ : ℝ)).exp.neg
    convert this using 1
    simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
    ring
  have hlim : Tendsto (fun R : ℝ => -exp (-2⁻¹ * R ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => -2⁻¹ * R ^ 2) atTop atBot :=
      tendsto_neg_const_mul_pow_atTop two_ne_zero (by norm_num)
    simpa using (tendsto_exp_atBot.comp h1).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrable_mul_exp_neg_mul_sq (by norm_num)).integrableOn hlim]
  ring

/-- The radial factor of the planar Gaussian beyond radius `a ≥ 0`. -/
theorem lintegral_radial_Ici {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ R in Ici a, ENNReal.ofReal ((2 * π)⁻¹ * (R * exp (-2⁻¹ * R ^ 2))) =
      ENNReal.ofReal ((2 * π)⁻¹ * exp (-2⁻¹ * a ^ 2)) := by
  rw [← setLIntegral_congr Ioi_ae_eq_Ici, ← ofReal_integral_eq_lintegral_ofReal,
    integral_const_mul, integral_Ioi_mul_exp_neg_half_sq]
  · exact ((integrable_mul_exp_neg_mul_sq (by norm_num)).const_mul _).integrableOn
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => ?_)
    have : 0 < r := lt_of_le_of_lt ha hr
    positivity

/-! ### Decay of the planar angle law -/

/-- **Decay of the planar angle law.** For independent standard Gaussians and `φ ≥ 0`, the
event `|cos φ Z₁ - c| ≤ sin φ |Z₂|` has probability at most `(2/π) φ exp (-c²/2)`. -/
theorem prod_gaussianReal_cos_sin_le {φ : ℝ} (hφ : 0 ≤ φ) (c : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1))
        {p : ℝ × ℝ | |cos φ * p.1 - c| ≤ sin φ * |p.2|} ≤
      ENNReal.ofReal (2 / π * φ * exp (-2⁻¹ * c ^ 2)) := by
  set A : Set (ℝ × ℝ) := {p | |cos φ * p.1 - c| ≤ sin φ * |p.2|} with hA
  have hAm : MeasurableSet A := measurableSet_le (by fun_prop) (by fun_prop)
  set B : Set (ℝ × ℝ) := {q | |cos φ * (q.1 * cos q.2) - c| ≤ sin φ * |q.1 * sin q.2|} with hB
  set f : ℝ → ℝ≥0∞ := fun R => ENNReal.ofReal ((2 * π)⁻¹ * (R * exp (-2⁻¹ * R ^ 2))) with hf
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    withDensity_apply _ hAm, ← Measure.volume_eq_prod, ← lintegral_indicator hAm,
    ← lintegral_comp_polarCoord_symm]
  have hint : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • A.indicator
          (fun z => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) (polarCoord.symm p) =
        f p.1 * B.indicator 1 p := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    have hiff : (r * cos θ, r * sin θ) ∈ A ↔ (r, θ) ∈ B := Iff.rfl
    simp only [polarCoord_symm_apply, smul_eq_mul]
    by_cases hθ : (r, θ) ∈ B
    · rw [indicator_of_mem (hiff.2 hθ), indicator_of_mem hθ, Pi.one_apply, mul_one,
        gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
        gaussianPDFReal_mul_polar, ← ENNReal.ofReal_mul hr.le]
      congr 1
      ring
    · rw [indicator_of_notMem (mt hiff.1 hθ), indicator_of_notMem hθ, mul_zero, mul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hint,
    polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans ?_
  have hslice : ∀ R ∈ Ioi (0 : ℝ), ∫⁻ ψ in Ioo (-π) π, f R * B.indicator 1 (R, ψ) ≤
      (Ici |c|).indicator (fun R => f R * ENNReal.ofReal (4 * φ)) R := by
    intro R hR
    have hR : 0 < R := hR
    have hS : MeasurableSet {ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have heq : (fun ψ => B.indicator (1 : ℝ × ℝ → ℝ≥0∞) (R, ψ)) =
        {ψ : ℝ | |cos φ * (R * cos ψ) - c| ≤ sin φ * |R * sin ψ|}.indicator 1 := rfl
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, heq, lintegral_indicator_one hS,
      Measure.restrict_apply hS, indicator_mul_right]
    gcongr
    exact volume_polar_event_le hφ hR
  calc ∫⁻ R in Ioi 0, ∫⁻ ψ in Ioo (-π) π, f R * B.indicator 1 (R, ψ)
      ≤ ∫⁻ R in Ioi 0, (Ici |c|).indicator (fun R => f R * ENNReal.ofReal (4 * φ)) R :=
        setLIntegral_mono' measurableSet_Ioi hslice
    _ ≤ ∫⁻ R, (Ici |c|).indicator (fun R => f R * ENNReal.ofReal (4 * φ)) R :=
        setLIntegral_le_lintegral _ _
    _ = (∫⁻ R in Ici |c|, f R) * ENNReal.ofReal (4 * φ) := by
        rw [lintegral_indicator measurableSet_Ici, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (2 / π * φ * exp (-2⁻¹ * c ^ 2)) := by
        rw [hf, lintegral_radial_Ici (abs_nonneg c), ← ENNReal.ofReal_mul (by positivity),
          sq_abs]
        congr 1
        field_simp
        ring

/-- The angle `arctan (√r / √s)` has cosine `√s / √(s + r)` and sine `√r / √(s + r)`. -/
theorem cos_sin_arctan_sqrt_div {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    cos (arctan (√r / √s)) = √s / √(s + r) ∧ sin (arctan (√r / √s)) = √r / √(s + r) := by
  have hs' : 0 < √s := Real.sqrt_pos.2 hs
  have hk : √(1 + (√r / √s) ^ 2) = √(s + r) / √s := by
    rw [div_pow, sq_sqrt hr, sq_sqrt hs.le, show 1 + r / s = (s + r) / s by field_simp,
      Real.sqrt_div (by linarith)]
  rw [cos_arctan, sin_arctan, hk]
  constructor <;> field_simp

/-- **Decay of the crossing event.** For independent centered Gaussians `X` and `Y` of
variances `s > 0` and `r`, the event `|X - c| ≤ |Y|` has probability at most
`(2/π) arctan (√r / √s) exp (-c² / (2 (s + r)))`. -/
theorem prod_gaussianReal_abs_sub_le_abs_exp (s r : ℝ≥0) (hs : s ≠ 0) (c : ℝ) :
    ((gaussianReal 0 s).prod (gaussianReal 0 r)) {p : ℝ × ℝ | |p.1 - c| ≤ |p.2|} ≤
      ENNReal.ofReal (2 / π * arctan (√(r : ℝ) / √(s : ℝ)) *
        exp (-(c ^ 2) / (2 * ((s : ℝ) + r)))) := by
  have hs' : (0 : ℝ) < s := by positivity
  obtain ⟨hcos, hsin⟩ := cos_sin_arctan_sqrt_div hs' (NNReal.coe_nonneg r)
  set L := √((s : ℝ) + r) with hL
  have hL0 : 0 < L := Real.sqrt_pos.2 (by positivity)
  set φ := arctan (√(r : ℝ) / √(s : ℝ)) with hφ
  rw [← gaussianReal_map_sqrt_mul s, ← gaussianReal_map_sqrt_mul r,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) (by fun_prop))]
  have hpre : Prod.map (fun x => √(s : ℝ) * x) (fun x => √(r : ℝ) * x) ⁻¹'
      {p : ℝ × ℝ | |p.1 - c| ≤ |p.2|} =
        {p : ℝ × ℝ | |cos φ * p.1 - c / L| ≤ sin φ * |p.2|} := by
    ext p
    simp only [mem_preimage, Prod.map_fst, Prod.map_snd, mem_ofPred_eq, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), hcos, hsin]
    have e1 : √(s : ℝ) / L * p.1 - c / L = (√(s : ℝ) * p.1 - c) / L := by
      field_simp
    have e2 : √(r : ℝ) / L * |p.2| = √(r : ℝ) * |p.2| / L := by
      field_simp
    rw [e1, e2, abs_div, abs_of_pos hL0, div_le_div_iff_of_pos_right hL0]
  rw [hpre]
  refine (prod_gaussianReal_cos_sin_le (arctan_nonneg.2 (by positivity)) _).trans_eq ?_
  have he : -2⁻¹ * (c / L) ^ 2 = -(c ^ 2) / (2 * ((s : ℝ) + r)) := by
    rw [div_pow, hL, sq_sqrt (by positivity)]
    field_simp
  rw [he]

/-- **Threshold decay of crossings** for coefficient vectors of equal norm with nonzero
sum. -/
theorem gaussPi_between_le_arctan_exp {ι : Type} [Fintype ι] (α β : ι → ℝ)
    (hnorm : ∑ i, α i ^ 2 = ∑ i, β i ^ 2) (hsum : 0 < ∑ i, (α i + β i) ^ 2) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      2 / π * arctan (√(∑ i, (β i - α i) ^ 2) / √(∑ i, (α i + β i) ^ 2)) *
        exp (-(t ^ 2) / (2 * ∑ i, α i ^ 2)) := by
  set a : ι → ℝ := fun i => β i - α i with ha
  set b : ι → ℝ := fun i => α i + β i with hb
  have hba : ∑ i, b i * a i = 0 := by
    have h : ∀ i, b i * a i = β i ^ 2 - α i ^ 2 := fun i => by simp only [ha, hb]; ring
    simp_rw [h, Finset.sum_sub_distrib, hnorm, sub_self]
  have hsr : ∑ i, b i ^ 2 + ∑ i, a i ^ 2 = 4 * ∑ i, α i ^ 2 := by
    have h : ∀ i, b i ^ 2 + a i ^ 2 = 2 * α i ^ 2 + 2 * β i ^ 2 := fun i => by
      simp only [ha, hb]; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← hnorm]
    ring
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
  have hk : 0 ≤ arctan (√(∑ i, a i ^ 2) / √(∑ i, b i ^ 2)) := arctan_nonneg.2 (by positivity)
  calc (gaussPi ι).real {ω | Between t (form α ω) (form β ω)}
      ≤ (gaussPi ι).real ((fun ω => (form b ω, form a ω)) ⁻¹' S) := measureReal_mono hsub
    _ = ((gaussianReal 0 (∑ i, b i ^ 2).toNNReal).prod
          (gaussianReal 0 (∑ i, a i ^ 2).toNNReal)).real S := by
        rw [← map_measureReal_apply hpair hSm, gaussPi_map_form_pair b a hba]
    _ ≤ _ := by
        refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
        refine (prod_gaussianReal_abs_sub_le_abs_exp _ _ hs0 (2 * t)).trans_eq ?_
        rw [Real.coe_toNNReal _ (hnn a), Real.coe_toNNReal _ (hnn b), hsr]
        congr 3
        ring

/-- **Threshold decay of crossings** for unit forms: a threshold `t` separates two unit
Gaussian forms of correlation `ρ` with probability at most `exp (-t²/2) arccos ρ / π`. -/
theorem gaussPi_between_le_exp_arccos {ι : Type} [Fintype ι] {α β : ι → ℝ}
    (hα : ∑ i, α i ^ 2 = 1) (hβ : ∑ i, β i ^ 2 = 1) (hx : -1 < ∑ i, α i * β i) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      exp (-(t ^ 2) / 2) * (arccos (∑ i, α i * β i) / π) := by
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
  refine (gaussPi_between_le_arctan_exp α β (by rw [hα, hβ]) (by rw [hplus]; linarith)
    t).trans_eq ?_
  rw [hplus, hminus, hα, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num),
    mul_div_mul_left _ _ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne',
    show √(1 - x) / √(1 + x) = tanHalf x from rfl, ← two_mul_arctan_tanHalf hx hx1, mul_one]
  ring

end Algebraic.Cutwidth.Gaussian.Internal
