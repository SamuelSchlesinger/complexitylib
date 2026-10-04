/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Assembly
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Grid

/-!
# Choosing the layout parameters

For fixed parameters, a good sample exists once the graph is large enough. As the decay
rate `q` increases to `1/√2`, the kernel correlation `2q/(1+q²)` increases to `2√2/3`,
where `√(1-ρ)/√(1+ρ) = 3 - 2√2`; the truncation error `3 (2q²)^R` vanishes as `R` grows.
A fine threshold grid with small deviations then brings the prefix-cut coefficient within
any positive slack of `(3/π)(3 - 2√2)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

/-- **Fixed parameters.** Every large cubic graph has an injective key whose prefix cuts
are at most `layoutBound ρ₀ T ε M` times the number of vertices. -/
theorem exists_key_of_parameters {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ}
    (hρ₀ : -1 < ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ}
    (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M) :
    ∃ N₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
      ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
        ((H.cutFinset (Finset.univ.filter fun w => key w < t)).card : ℝ) ≤
          layoutBound ρ₀ T ε M * Fintype.card W := by
  refine ⟨⌈(3 * M + 2) * (overlapBound R : ℝ) / ε ^ 2⌉₊,
    fun W _ _ H _ regular large => ?_⟩
  have large' : (3 * M + 2) * (overlapBound R : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨ω, hω⟩ := exists_good_sample H regular hq0 R hρ₀ hρ hT hε hM large'
  exact ⟨scoreKey (score H q R ω), scoreKey_injective _,
    fun t => (hω t).trans_eq (mul_comm _ _)⟩

/-- The crossing ratio `√(1-ρ)/√(1+ρ)`. -/
noncomputable def crossRatio (ρ : ℝ) : ℝ :=
  Real.sqrt (1 - ρ) / Real.sqrt (1 + ρ)

theorem crossBound_eq (ρ : ℝ) : crossBound ρ = 2 / Real.pi * crossRatio ρ := rfl

theorem crossRatio_limit : crossRatio (2 * Real.sqrt 2 / 3) = 3 - 2 * Real.sqrt 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hge : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hminus : 1 - 2 * Real.sqrt 2 / 3 = (Real.sqrt 2 - 1) ^ 2 / 3 := by
    ring_nf; rw [h2]; ring
  have hplus : 1 + 2 * Real.sqrt 2 / 3 = (Real.sqrt 2 + 1) ^ 2 / 3 := by
    ring_nf; rw [h2]; ring
  unfold crossRatio
  rw [hminus, hplus, Real.sqrt_div' _ (by norm_num), Real.sqrt_div' _ (by norm_num),
    Real.sqrt_sq (by linarith), Real.sqrt_sq (by linarith),
    div_div_div_cancel_right₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
  rw [div_eq_iff (by linarith)]
  ring_nf
  rw [h2]
  ring

theorem continuousAt_crossRatio {ρ : ℝ} (hρ : -1 < ρ) : ContinuousAt crossRatio ρ := by
  unfold crossRatio
  refine ContinuousAt.div ?_ ?_ (Real.sqrt_pos.mpr (by linarith)).ne'
  · exact (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt
  · exact (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt

theorem continuous_correlation : Continuous fun q : ℝ => 2 * q / (1 + q ^ 2) :=
  (continuous_const.mul continuous_id).div (continuous_const.add (continuous_pow 2))
    fun q => by positivity

theorem correlation_limit :
    2 * (Real.sqrt 2 / 2) / (1 + (Real.sqrt 2 / 2) ^ 2) = 2 * Real.sqrt 2 / 3 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [div_pow, h2]
  field_simp
  ring

theorem gaussianCutwidthCoefficient_ge : 3 / 40 ≤ gaussianCutwidthCoefficient := by
  have hsqrt : Real.sqrt 2 < 29 / 20 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  unfold gaussianCutwidthCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
  nlinarith [Real.pi_le_four]

/-- **Parameters.** For every positive slack some admissible parameters bring the layout
bound within that slack of `(3/π)(3 - 2√2)`. -/
theorem exists_parameters {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ T ε : ℝ) (M : ℕ), 0 ≤ q ∧ -1 < ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      layoutBound ρ₀ T ε M ≤ gaussianCutwidthCoefficient + ξ := by
  set g : ℝ := 2 * Real.sqrt 2 / 3 with hg
  have hsqrt_lt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hg1 : 0 < g := by positivity
  -- A correlation target `ρ₀ < g` with nearly optimal crossing ratio.
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (continuousAt_crossRatio (by linarith : -1 < g)) (Real.pi * ξ / 6) (by positivity)
  set ρ₀ := g - min η (1 / 2) / 2 with hρ₀
  have hmin : 0 < min η (1 / 2) := lt_min hη (by norm_num)
  have hρ₀g : ρ₀ < g := by rw [hρ₀]; linarith
  have hρ₀low : -1 < ρ₀ := by
    rw [hρ₀]; linarith [min_le_right η (1 / 2)]
  have hratio : crossRatio ρ₀ ≤ 3 - 2 * Real.sqrt 2 + Real.pi * ξ / 6 := by
    have hdist : dist ρ₀ g < η := by
      rw [Real.dist_eq, hρ₀, abs_of_neg (by linarith)]
      linarith [min_le_left η (1 / 2)]
    have := hcont hdist
    rw [Real.dist_eq, crossRatio_limit] at this
    linarith [le_abs_self (crossRatio ρ₀ - (3 - 2 * Real.sqrt 2))]
  -- A decay rate `q < 1/√2` whose correlation exceeds the target.
  set q₀ : ℝ := Real.sqrt 2 / 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  obtain ⟨δ, hδ, hκ⟩ := Metric.continuousAt_iff.mp continuous_correlation.continuousAt
    ((g - ρ₀) / 2) (by linarith)
  set q := q₀ - min δ q₀ / 2 with hq
  have hminq : 0 < min δ q₀ := lt_min hδ hq₀pos
  have hq0 : 0 ≤ q := by rw [hq]; linarith [min_le_right δ q₀]
  have hqq₀ : q < q₀ := by rw [hq]; linarith
  have hκq : g - (g - ρ₀) / 2 < 2 * q / (1 + q ^ 2) := by
    have hdist : dist q q₀ < δ := by
      rw [Real.dist_eq, hq, abs_of_neg (by linarith)]
      linarith [min_le_left δ q₀]
    have := hκ hdist
    rw [Real.dist_eq, hq₀, correlation_limit, ← hg] at this
    linarith [neg_abs_le (2 * q / (1 + q ^ 2) - g)]
  -- A truncation radius with small boundary error.
  have hdecay : 2 * q ^ 2 < 1 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : q ^ 2 < q₀ ^ 2 := by gcongr
    rw [hq₀, div_pow, h2] at this
    linarith
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < (g - ρ₀) / 6) hdecay
  have hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R := by linarith
  -- The grid and the deviation slack.
  set ε := min (ξ / 16) (1 / 100) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  set M : ℕ := ⌈120 / ξ⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : 120 / ξ ≤ M := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (120 / ξ)]
  refine ⟨q, R, ρ₀, 10, ε, M, hq0, hρ₀low, hρ, by norm_num, hεpos, hMpos, ?_⟩
  have hcoef := gaussianCutwidthCoefficient_ge
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  unfold layoutBound
  refine max_le ?_ ?_
  · have : ε ≤ 1 / 100 := min_le_right _ _
    linarith
  · have hεξ : ε ≤ ξ / 16 := min_le_left _ _
    have hcross : 3 / 2 * crossBound ρ₀ ≤ gaussianCutwidthCoefficient + ξ / 2 := by
      rw [crossBound_eq, gaussianCutwidthCoefficient]
      have : 3 / 2 * (2 / Real.pi * crossRatio ρ₀) = 3 / Real.pi * crossRatio ρ₀ := by ring
      rw [this]
      calc 3 / Real.pi * crossRatio ρ₀ ≤
            3 / Real.pi * (3 - 2 * Real.sqrt 2 + Real.pi * ξ / 6) := by
            gcongr
        _ = 3 / Real.pi * (3 - 2 * Real.sqrt 2) + ξ / 2 := by
            field_simp
            ring
    have hsqrtpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.two_le_pi])
    have hgrid : 3 * (2 * 10 / M) / Real.sqrt (2 * Real.pi) ≤ ξ / 4 := by
      rw [div_le_iff₀ (by positivity)]
      calc 3 * (2 * 10 / (M : ℝ)) = 60 / M := by ring
        _ ≤ ξ / 2 := by
            rw [div_le_iff₀ hMpos']
            have := mul_le_mul_of_nonneg_left hMR hξ.le
            rw [mul_div_cancel₀ _ hξ.ne'] at this
            linarith
        _ ≤ ξ / 4 * Real.sqrt (2 * Real.pi) := by nlinarith
    linarith

/-- **The Gaussian cubic cutwidth bound.** For every positive slack, every large cubic graph
has an injective key whose prefix cuts are at most `((3/π)(3 - 2√2) + ξ) h`. -/
theorem exists_key_bound {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
      ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
        ((H.cutFinset (Finset.univ.filter fun w => key w < t)).card : ℝ) ≤
          (gaussianCutwidthCoefficient + ξ) * Fintype.card W := by
  obtain ⟨q, R, ρ₀, T, ε, M, hq0, hρ₀, hρ, hT, hε, hM, hbound⟩ := exists_parameters hξ
  obtain ⟨N₀, hN₀⟩ := exists_key_of_parameters hq0 R hρ₀ hρ hT hε hM
  refine ⟨N₀, fun W _ _ H _ regular large => ?_⟩
  obtain ⟨key, injective, hkey⟩ := hN₀ W H regular large
  exact ⟨key, injective,
    fun t => (hkey t).trans (mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _))⟩

end Algebraic.Cutwidth.Gaussian.Internal
