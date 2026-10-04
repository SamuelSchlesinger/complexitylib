/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Internal.Assembly
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Limit

/-!
# Choosing the band-jump parameters

The edge-score parameters of `Gaussian.Frontier` bring the per-vertex straddling bound within
any slack of the frontier coefficient. The band-jump decomposition multiplies it by
`exp (-c²/2)`; a long fine grid, small deviations, and a small Markov threshold bring every bag
within any slack of `exp (-c²/2)` times the frontier coefficient, once the subcriticality
hypothesis supplies a cluster size `K` and the graph is large enough that `K` is negligible.

At `c = 4/25` the doubled coefficient is at most `5/18`, because `2 p ≤ 9/32` and
`exp (-8/625) ≤ 80/81`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

/-- A correlation target of at least `17/32` forces a decay rate below `1/√2`. -/
theorem two_mul_sq_lt_one_of_le {q : ℝ} {R : ℕ} {ρ₀ : ℝ} (hρ₀ : 17 / 32 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) : 2 * q ^ 2 < 1 := by
  by_contra hge
  push Not at hge
  have h1 : 1 ≤ (2 * q ^ 2) ^ R := one_le_pow₀ hge
  have h2 : 2 * q / (1 + q ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (q - 1)]
  linarith

/-- **Fixed parameters.** Under the subcriticality hypothesis, every large cubic graph has a
band-jump decomposition with bags of at most `(bandLayoutBound ρ₀ c T ε η M + ε) h`
vertices. -/
theorem exists_band_of_parameters {q : ℝ} (hq0 : 0 ≤ q) (R : ℕ) {ρ₀ : ℝ}
    (hρ₀ : 17 / 32 ≤ ρ₀) (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {c T ε η : ℝ} (hc : 0 < c) (hcT : c < T) (hε : 0 < ε) (hη : 0 < η) {M : ℕ} (hM : 0 < M)
    (hband : BandSubcritical q R c) :
    ∃ N₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
      ∃ D : PathDecomposition H, ∀ k,
        ((D.bag k).card : ℝ) ≤ (bandLayoutBound ρ₀ c T ε η M + ε) * Fintype.card W := by
  obtain ⟨K, hK⟩ := hband η hη
  refine ⟨max ⌈(10 * M + 10) * (overlapBound (R + 1) : ℝ) / ε ^ 2⌉₊ ⌈(K : ℝ) / ε⌉₊,
    fun W _ _ H _ regular large => ?_⟩
  have large₁ : (10 * M + 10) * (overlapBound (R + 1) : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast (le_max_left _ _).trans_lt large)
  have large₂ : (K : ℝ) / ε < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast (le_max_right _ _).trans_lt large)
  obtain ⟨D, hD⟩ := exists_good_band_sample H regular hq0 R hρ₀ hρ hc hcT hε hη hM
    (hK W H regular) large₁
  refine ⟨D, fun k => (hD k).trans ?_⟩
  have hK' : (K : ℝ) ≤ ε * Fintype.card W := by
    rw [div_lt_iff₀ hε] at large₂
    linarith
  linarith

/-- **Parameters.** For every positive slack some admissible parameters bring the band-jump
bound within that slack of `exp (-c²/2)` times the frontier coefficient. -/
theorem exists_band_parameters {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ₀ T ε η : ℝ) (M : ℕ), 0 ≤ q ∧ 17 / 32 ≤ ρ₀ ∧
      ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ c < T ∧ 0 < ε ∧ 0 < η ∧ 0 < M ∧
      bandLayoutBound ρ₀ c T ε η M + ε ≤ Real.exp (-(c ^ 2) / 2) * frontierCoefficient + ξ := by
  obtain ⟨q, R, ρ₀, T₀, ε₀, M₀, hq0, hρ₀, hρ, hT₀, hε₀, -, hbound₀⟩ :=
    exists_frontier_parameters (by positivity : 0 < ξ / 4)
  -- The straddling bound of the chosen correlation target.
  have hfb : frontierBound ρ₀ ≤ frontierCoefficient + ξ / 4 := by
    refine le_trans ?_ hbound₀
    unfold frontierLayoutBound
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ 3 * (2 * T₀ / M₀) / Real.sqrt (2 * Real.pi) := by positivity
    linarith
  set e := Real.exp (-(c ^ 2) / 2) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg c])
  have hfC := frontierCoefficient_pos
  -- The grid length, the grid, and the slacks.
  set L : ℝ := 6 / ξ + 1 with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith [div_pos (by norm_num : (0 : ℝ) < 6) hξ]
  have hLξ : 3 ≤ ξ / 2 * L := by
    rw [hL, mul_add, show ξ / 2 * (6 / ξ) = 3 by field_simp; ring]
    linarith
  set M : ℕ := ⌈12 * L / ξ⌉₊ + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos _
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hML : 12 * L / ξ ≤ M := by
    rw [hM]; push_cast; linarith [Nat.le_ceil (12 * L / ξ)]
  refine ⟨q, R, ρ₀, c + L, ξ / 16, ξ / 8, M, hq0, hρ₀, hρ, by linarith, by positivity,
    by positivity, hMpos, ?_⟩
  unfold bandLayoutBound
  rw [show c + L - c = L by ring, ← max_add_add_right]
  refine max_le ?_ ?_
  · -- The tails.
    have hcL : L ≤ c + L := by linarith
    have hsq : L ≤ (c + L) ^ 2 := by nlinarith
    have htail : 3 / (c + L) ^ 2 ≤ ξ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have : 0 ≤ e * frontierCoefficient := by positivity
    linarith
  · -- The grid and the slacks.
    have hsqrtpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
      (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.two_le_pi])
    have hgrid : 3 * (L / M) / Real.sqrt (2 * Real.pi) ≤ ξ / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have hLM : L / M ≤ ξ / 12 := by
        rw [div_le_iff₀ hMpos']
        have := mul_le_mul_of_nonneg_left hML hξ.le
        rw [mul_div_cancel₀ _ hξ.ne'] at this
        linarith
      nlinarith
    have hdecay : e * frontierBound ρ₀ ≤ e * frontierCoefficient + ξ / 4 := by
      have := mul_le_mul_of_nonneg_left hfb he0.le
      nlinarith
    linarith

/-- **The band-jump cubic pathwidth bound**, conditional on subcritical band clusters. -/
theorem exists_pathwidthBound_band {c : ℝ} (hc : 0 < c)
    (hband : ∀ (q : ℝ) (R : ℕ), 0 ≤ q → 2 * q ^ 2 < 1 → BandSubcritical q R c) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, PathwidthBound (Real.exp (-(c ^ 2) / 2) * frontierCoefficient) ξ N₀ := by
  obtain ⟨q, R, ρ₀, T, ε, η, M, hq0, hρ₀, hρ, hcT, hε, hη, hM, hbound⟩ :=
    exists_band_parameters hc hξ
  obtain ⟨N₀, hN₀⟩ := exists_band_of_parameters hq0 R hρ₀ hρ hc hcT hε hη hM
    (hband q R hq0 (two_mul_sq_lt_one_of_le hρ₀ hρ))
  refine ⟨N₀, fun W _ _ H _ regular large => ?_⟩
  obtain ⟨D, hD⟩ := hN₀ W H regular large
  refine ⟨D, fun k => (hD k).trans ?_⟩
  have hh0 : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hbound hh0]

/-- `exp (-(4/25)²/2) = exp (-8/625) ≤ 80/81`. -/
theorem exp_neg_four_div_twentyFive_sq_le :
    Real.exp (-((4 / 25 : ℝ) ^ 2) / 2) ≤ 80 / 81 := by
  have h : -((4 / 25 : ℝ) ^ 2) / 2 = -(8 / 625) := by norm_num
  have h1 : (81 / 80 : ℝ) ≤ Real.exp (8 / 625) := by
    linarith [Real.add_one_le_exp (8 / 625 : ℝ)]
  have h2 : Real.exp (-(8 / 625)) * Real.exp (8 / 625) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [h]
  nlinarith [Real.exp_pos (-(8 / 625 : ℝ))]

/-- At `c = 4/25` the doubled band-jump coefficient is at most `5/18`. -/
theorem two_mul_exp_mul_frontierCoefficient_le :
    2 * (Real.exp (-((4 / 25 : ℝ) ^ 2) / 2) * frontierCoefficient) ≤ 5 / 18 := by
  have he := exp_neg_four_div_twentyFive_sq_le
  have he0 := Real.exp_pos (-((4 / 25 : ℝ) ^ 2) / 2)
  have hp := two_mul_frontierCoefficient_le
  have hp0 := frontierCoefficient_pos
  nlinarith

end Algebraic.Cutwidth.Gaussian.Internal
