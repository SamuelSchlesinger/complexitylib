/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.VertexGaussian

/-!
# The bounded-degree vertex-layout coefficient

The limiting adjacent correlation is `2 sqrt(d - 1) / d`. Consequently Gaussian vertex
layouts have at most `arccos(2 sqrt(d - 1) / d) / pi` times the number of edges, plus an
arbitrarily small linear error. At degree four this per-edge coefficient is exactly `1/6`.
-/

@[expose] public section

namespace Complexity.Frontier.Gaussian

open Finset

/-- The kernel correlation `2√(d - 1)/d` of adjacent vertices in degree `d`. -/
noncomputable def vertexCorrelation (d : ℕ) : ℝ := 2 * Real.sqrt (d - 1) / d

/-- The edge-crossing probability `arccos(ρ_d)/π` of Gaussian vertex scores. -/
noncomputable def vertexCoefficient (d : ℕ) : ℝ := Real.arccos (vertexCorrelation d) / Real.pi

theorem vertexCorrelation_pos {d : ℕ} (hd : 2 ≤ d) : 0 < vertexCorrelation d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have : 0 < (d : ℝ) - 1 := by linarith
  unfold vertexCorrelation
  positivity

/-- The radial kernel reaches every correlation strictly below its limiting value. -/
theorem exists_decay_radius_degree {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : ρ < vertexCorrelation d) :
    ∃ (q : ℝ) (R : ℕ), 0 ≤ q ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1 : ℕ) * q ^ 2) ^ R := by
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by dsimp [D]; exact_mod_cast hd
  set g := vertexCorrelation d
  set q₀ := Real.sqrt (D - 1) / (D - 1)
  have hu : 0 < D - 1 := by linarith
  have hq₀ : 0 < q₀ := by dsimp [q₀]; positivity
  have hs : Real.sqrt (D - 1) ^ 2 = D - 1 := Real.sq_sqrt hu.le
  have hsq : q₀ ^ 2 = 1 / (D - 1) := by dsimp [q₀]; rw [div_pow, hs]; field_simp
  have hlim : 2 * q₀ / (1 + q₀ ^ 2) = g := by
    rw [hsq]
    dsimp [q₀, g, vertexCorrelation]
    change 2 * (Real.sqrt (D - 1) / (D - 1)) / (1 + 1 / (D - 1)) =
      2 * Real.sqrt (D - 1) / D
    field_simp; ring
  obtain ⟨δ, hδ, hκ⟩ := Metric.continuousAt_iff.mp continuous_correlation.continuousAt
    ((g - ρ) / 2) (by linarith)
  set q := q₀ - min δ q₀ / 2
  have hmin : 0 < min δ q₀ := lt_min hδ hq₀
  have hq0 : 0 ≤ q := by dsimp [q]; linarith [min_le_right δ q₀]
  have hqq : q < q₀ := by dsimp [q]; linarith
  have hκq : g - (g - ρ) / 2 < 2 * q / (1 + q ^ 2) := by
    have hdist : dist q q₀ < δ := by
      rw [Real.dist_eq, show q - q₀ = -(min δ q₀ / 2) by dsimp [q]; ring,
        abs_neg, abs_of_pos (by positivity)]
      linarith [min_le_left δ q₀]
    have H := hκ hdist
    rw [Real.dist_eq, hlim] at H
    linarith [neg_abs_le (2 * q / (1 + q ^ 2) - g)]
  have hdecay : (d - 1 : ℕ) * q ^ 2 < (1 : ℝ) := by
    have hq2 : q ^ 2 < q₀ ^ 2 := by gcongr
    have hq2' := mul_lt_mul_of_pos_left hq2 hu
    rw [hsq, mul_one_div_cancel hu.ne'] at hq2'
    simpa only [Nat.cast_sub (by lia : 1 ≤ d), Nat.cast_one, D] using hq2'
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < (g - ρ) / (2 * D)) hdecay
  have hR' := mul_lt_mul_of_pos_left hR (by linarith : 0 < D)
  have hcancel : D * ((g - ρ) / (2 * D)) = (g - ρ) / 2 := by field_simp
  rw [hcancel] at hR'
  exact ⟨q, R, hq0, by linarith⟩

/-- **Gaussian vertex layouts in every fixed degree.** The error is measured per vertex;
the leading coefficient is measured per edge. -/
theorem vertexLayout_bound {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v, H.degree v ≤ d) → N₀ < Fintype.card W →
      ∃ key : W → ℕ, Function.Injective key ∧ ∀ t,
        ((H.crossingFinset {v | key v < t}).card : ℝ) ≤
          vertexCoefficient d * H.edgeFinset.card + ξ * Fintype.card W := by
  set D : ℝ := (d : ℝ)
  have hD : 2 ≤ D := by dsimp [D]; exact_mod_cast hd
  set g := vertexCorrelation d
  have hg : 0 < g := vertexCorrelation_pos hd
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (Real.continuous_arccos.continuousAt (x := g)) (Real.pi * ξ / (4 * D)) (by positivity)
  set ρ := g - min η g / 2
  have hmin : 0 < min η g := lt_min hη hg
  have hρg : ρ < g := by dsimp [ρ]; linarith
  have hρ0 : -1 < ρ := by dsimp [ρ]; linarith [min_le_right η g]
  have hcoef : Real.arccos ρ / Real.pi ≤ vertexCoefficient d + ξ / (4 * D) := by
    have hdist : dist ρ g < η := by
      rw [Real.dist_eq, show ρ - g = -(min η g / 2) by dsimp [ρ]; ring,
        abs_neg, abs_of_pos (by positivity)]
      linarith [min_le_left η g]
    have H := (le_abs_self _).trans (hcont hdist).le
    rw [div_le_iff₀ Real.pi_pos]
    dsimp [vertexCoefficient]
    have heq : (Real.arccos g / Real.pi + ξ / (4 * D)) * Real.pi =
        Real.arccos g + Real.pi * ξ / (4 * D) := by field_simp
    rw [show vertexCorrelation d = g from rfl, heq]
    linarith
  obtain ⟨q, R, hq, hcorr⟩ := exists_decay_radius_degree hd hρg
  set T := 1 + 4 * D / ξ
  set ε := ξ / (4 * (D + 1))
  set M : ℕ := ⌈8 * D * T / ξ⌉₊ + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hM : 0 < M := Nat.succ_pos _
  have hMR : 8 * D * T / ξ ≤ (M : ℝ) := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (8 * D * T / ξ)]
  have htail : D / T ^ 2 ≤ ξ / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hT)]
    have hx : 0 ≤ 4 * D / ξ := by positivity
    have hsq : 4 * D / ξ ≤ T ^ 2 := by dsimp [T]; nlinarith [sq_nonneg (4 * D / ξ)]
    have H := mul_le_mul_of_nonneg_left hsq hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at H
    linarith
  have hgrid : D * (2 * T / M) / Real.sqrt (2 * Real.pi) ≤ ξ / 4 := by
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by linarith [Real.two_le_pi])
    have hfrac : D * (2 * T / M) ≤ ξ / 4 := by
      rw [← mul_div_assoc, div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)]
      have H := (div_le_iff₀ hξ).mp hMR
      linarith
    exact (div_le_self (by positivity) hsqrt).trans hfrac
  have herr : D / T ^ 2 + D * (2 * T / M) / Real.sqrt (2 * Real.pi) + (D + 1) * ε ≤
      3 * ξ / 4 := by
    have heq : (D + 1) * ε = ξ / 4 := by dsimp [ε]; field_simp
    linarith
  refine ⟨⌈(M * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2⌉₊,
    fun W _ H _ degree large => ?_⟩
  have hlarge : (M * (D + 1) + 2) * (vertexOverlap d R : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨key, hinj, hcut⟩ := exists_vertex_sample H hd degree hq R hρ0 hcorr hT hε hM hlarge
  refine ⟨key, hinj, fun t => (hcut t).trans ?_⟩
  have hE : (H.edgeFinset.card : ℝ) ≤ D * Fintype.card W := by
    dsimp [D]
    exact_mod_cast card_edges_le_degree_mul H degree
  have herror : ξ / (4 * D) * H.edgeFinset.card ≤ ξ / 4 * Fintype.card W := by
    have h := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ ξ / (4 * D))
    convert h using 1; field_simp
  have h1 := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) H.edgeFinset.card)
  have h2 := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (α := ℝ) (Fintype.card W))
  nlinarith

/-- Degree four gives an exact per-edge crossing coefficient of one sixth. -/
theorem vertexCoefficient_four : vertexCoefficient 4 = 1 / 6 := by
  have harg : vertexCorrelation 4 = Real.sqrt 3 / 2 := by norm_num [vertexCorrelation]; ring
  rw [vertexCoefficient, harg, ← Real.cos_pi_div_six,
    Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  field_simp

end Complexity.Frontier.Gaussian
