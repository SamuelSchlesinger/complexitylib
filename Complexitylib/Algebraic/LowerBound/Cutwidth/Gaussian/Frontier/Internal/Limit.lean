/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Assembly
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Limit
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Choosing the edge-score parameters

For fixed parameters, a good sample exists once the cubic graph is large. As the edge
correlation target increases to `2√2/3`, the per-vertex straddling bound
`(3/(2π)) arccos ((1 + 3ρ₀)/4)` decreases to `(3/(2π)) arccos ((1 + 2√2)/4)`; a fine grid with
small deviations brings every bag within any positive slack of that coefficient.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

/-- **Fixed parameters.** Every large cubic graph has an edge-score decomposition with bags
of at most `frontierLayoutBound ρ₀ T ε M` times the number of vertices. -/
theorem exists_frontier_of_parameters {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ}
    (hρ₀ : 17 / 32 ≤ ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) {T ε : ℝ}
    (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M) :
    ∃ N₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
      ∃ D : PathDecomposition H, ∀ k,
        ((D.bag k).card : ℝ) ≤ frontierLayoutBound ρ₀ T ε M * Fintype.card W := by
  refine ⟨⌈(3 * M + 3) * (overlapBound (R + 1) : ℝ) / ε ^ 2⌉₊,
    fun W _ _ H _ regular large => ?_⟩
  have large' : (3 * M + 3) * (overlapBound (R + 1) : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨D, hD⟩ := exists_good_frontier_sample H regular hq0 R hρ₀ hρ hT hε hM large'
  exact ⟨D, fun k => (hD k).trans_eq (by ring)⟩

theorem frontierCoefficient_eq :
    frontierCoefficient =
      3 / (2 * Real.pi) * Real.arccos ((1 + 3 * (2 * Real.sqrt 2 / 3)) / 4) := by
  rw [frontierCoefficient]
  congr 2
  ring

theorem frontierCoefficient_ge : 1 / 20 ≤ frontierCoefficient := by
  have hsqrt : Real.sqrt 2 < 71 / 50 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hpi4 := Real.pi_le_four
  have hθ : Real.pi / 30 ≤ Real.arccos ((1 + 2 * Real.sqrt 2) / 4) := by
    have hcos : (1 + 2 * Real.sqrt 2) / 4 ≤ Real.cos (Real.pi / 30) := by
      have := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 30)
      have hsq : (Real.pi / 30) ^ 2 ≤ (4 / 30) ^ 2 := by gcongr
      linarith
    calc Real.pi / 30 = Real.arccos (Real.cos (Real.pi / 30)) :=
          (Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])).symm
      _ ≤ _ := Real.arccos_le_arccos hcos
  unfold frontierCoefficient
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

theorem frontierCoefficient_pos : 0 < frontierCoefficient :=
  lt_of_lt_of_le (by norm_num) frontierCoefficient_ge

theorem arccos_frontier_pos : 0 < Real.arccos ((1 + 2 * Real.sqrt 2) / 4) := by
  have hsqrt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  exact Real.arccos_pos.mpr (by linarith)

/-- The circuit coefficient `1 + 1/(2p)` of the frontier coefficient `p`. -/
theorem one_add_inv_two_mul_frontierCoefficient :
    1 + 1 / (2 * frontierCoefficient) =
      1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) := by
  have h := arccos_frontier_pos
  unfold frontierCoefficient
  congr 1
  field_simp

/-- The frontier ordering coefficient `2p` is at most `9/32`. -/
theorem two_mul_frontierCoefficient_le : 2 * frontierCoefficient ≤ 9 / 32 := by
  have hlo : (141421 : ℝ) / 100000 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  set θ := 3 * Real.pi / 32 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hθlo : 0.29451 ≤ θ := by rw [hθ]; linarith
  have hθhi : θ ≤ 0.29453 := by rw [hθ]; linarith
  have hcosθ : Real.cos θ ≤ (1 + 2 * Real.sqrt 2) / 4 := by
    have hb := Real.cos_bound (x := θ) (by rw [abs_of_nonneg hθ0]; exact hθ1)
    rw [abs_of_nonneg hθ0] at hb
    have h2 : θ ^ 2 ≥ 0.29451 ^ 2 := by gcongr
    have h4 : θ ^ 4 ≤ 0.29453 ^ 4 := by gcongr
    nlinarith [(abs_sub_le_iff.mp hb).1]
  have harc : Real.arccos ((1 + 2 * Real.sqrt 2) / 4) ≤ θ :=
    (Real.arccos_le_arccos hcosθ).trans_eq
      (Real.arccos_cos hθ0 (by rw [hθ]; linarith [Real.pi_pos]))
  unfold frontierCoefficient
  rw [hθ] at harc
  have : 2 * (3 / (2 * Real.pi) * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) =
      3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4) / Real.pi := by
    field_simp
  rw [this, div_le_iff₀ Real.pi_pos]
  linarith

/-- **Parameters.** For every positive slack some admissible parameters bring the
edge-score bound within that slack of the frontier coefficient. -/
theorem exists_frontier_parameters {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ T ε : ℝ) (M : ℕ), 0 ≤ q ∧ 17 / 32 ≤ ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < T ∧ 0 < ε ∧ 0 < M ∧
      frontierLayoutBound ρ₀ T ε M ≤ frontierCoefficient + ξ := by
  set g : ℝ := 2 * Real.sqrt 2 / 3 with hg
  have hsqrt_lo : (7 : ℝ) / 5 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hsqrt_hi : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  -- A correlation target `ρ₀ < g` with nearly optimal straddling bound.
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    ((Real.continuous_arccos.comp (by fun_prop : Continuous fun ρ : ℝ => (1 + 3 * ρ) / 4)
      ).continuousAt (x := g)) (Real.pi * ξ / 6) (by positivity)
  set ρ₀ := g - min η (1 / 4) / 2 with hρ₀
  have hmin : 0 < min η (1 / 4) := lt_min hη (by norm_num)
  have hρ₀g : ρ₀ < g := by rw [hρ₀]; linarith
  have hρ₀low : 17 / 32 ≤ ρ₀ := by
    rw [hρ₀, hg]; linarith [min_le_right η (1 / 4)]
  have hbound : frontierBound ρ₀ ≤ frontierCoefficient + ξ / 4 := by
    have hdist : dist ρ₀ g < η := by
      rw [Real.dist_eq, hρ₀, abs_of_neg (by linarith)]
      linarith [min_le_left η (1 / 4)]
    have := hcont hdist
    simp only [Function.comp_apply, Real.dist_eq] at this
    have hle := (le_abs_self _).trans this.le
    rw [frontierBound, frontierCoefficient_eq, ← hg]
    have hpi : 0 < Real.pi := Real.pi_pos
    have : 3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ₀) / 4) ≤
        3 / (2 * Real.pi) * (Real.arccos ((1 + 3 * g) / 4) + Real.pi * ξ / 6) := by
      gcongr
      linarith
    calc _ ≤ _ := this
      _ = 3 / (2 * Real.pi) * Real.arccos ((1 + 3 * g) / 4) + ξ / 4 := by field_simp; ring
  obtain ⟨q, R, hq0, hρ⟩ := exists_decay_radius hρ₀g
  -- The grid and the deviation slack.
  set ε := min (ξ / 12) (1 / 100) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by norm_num)
  set M : ℕ := ⌈120 / ξ⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMR : 120 / ξ ≤ M := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (120 / ξ)]
  refine ⟨q, R, ρ₀, 10, ε, M, hq0, hρ₀low, hρ, by norm_num, hεpos, hMpos, ?_⟩
  have hcoef := frontierCoefficient_ge
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  unfold frontierLayoutBound
  refine max_le ?_ ?_
  · have : ε ≤ 1 / 100 := min_le_right _ _
    linarith
  · have hεξ : ε ≤ ξ / 12 := min_le_left _ _
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

/-- **The Gaussian cubic pathwidth bound.** -/
theorem exists_pathwidthBound_frontier {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, PathwidthBound frontierCoefficient ξ N₀ := by
  obtain ⟨q, R, ρ₀, T, ε, M, hq0, hρ₀, hρ, hT, hε, hM, hbound⟩ :=
    exists_frontier_parameters (by positivity : 0 < ξ / 2)
  obtain ⟨N₀, hN₀⟩ := exists_frontier_of_parameters hq0 R hρ₀ hρ hT hε hM
  refine ⟨N₀, fun W _ _ H _ regular large => ?_⟩
  obtain ⟨D, hD⟩ := hN₀ W H regular large
  refine ⟨D, fun k => (hD k).trans ?_⟩
  have hh0 : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hbound hh0]

end Algebraic.Cutwidth.Gaussian.Internal
