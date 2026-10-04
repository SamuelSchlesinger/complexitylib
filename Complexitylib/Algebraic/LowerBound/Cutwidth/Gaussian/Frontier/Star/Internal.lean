/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Crossing ratios in a star: proofs

Vectors are functions `ι → ℝ` with the dot product `∑ i, y i * x i`.

* Two unit vectors with inner product at least `κ` with a common unit vector satisfy
  `‖y - y'‖² ≤ 2 ‖y - x‖² + 2 ‖x - y'‖²`, which gives inner product at least `4κ - 3`.
* For the sum `S` of the vectors `y j`, `‖S‖²` is the family size plus the ordered-pair
  inner products, and Cauchy–Schwarz against the unit vector gives `‖S‖² ≥ (n κ)²`.
* On `[1/2, 1]`, `y = tanHalf x` satisfies `x = (1 - y²) / (1 + y²)` with `y² ≤ 1/3`, and
  the polynomial identity
  `(1 + y²) (4y₀² - (1 + y₀²)² (x - x₀) - 4y₀y) = 2 (y - y₀)² (1 - y₀² - 2y₀y)` gives the
  tangent bound `4y₀y ≤ 4y₀² - (1 + y₀²)² (x - x₀)`. Summing the tangent bound over a
  family whose arguments average at least `x₀` bounds the sum of crossing ratios.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

/-! ### Inner products of unit vectors -/

/-- Cauchy–Schwarz for unit vectors: their inner product is at most one. -/
theorem inner_le_one {ι : Type} [Fintype ι] {y y' : ι → ℝ}
    (hy : ∑ i, y i ^ 2 = 1) (hy' : ∑ i, y' i ^ 2 = 1) : ∑ i, y i * y' i ≤ 1 := by
  have h := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (y i - y' i)
  have e : ∑ i, (y i - y' i) ^ 2 = ∑ i, y i ^ 2 + ∑ i, y' i ^ 2 - 2 * ∑ i, y i * y' i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- Unit vectors close to a common unit vector are close to each other. -/
theorem le_inner_of_le_inner {ι : Type} [Fintype ι] {x y y' : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) (hy' : ∑ i, y' i ^ 2 = 1) {κ : ℝ}
    (hyx : κ ≤ ∑ i, y i * x i) (hy'x : κ ≤ ∑ i, y' i * x i) :
    4 * κ - 3 ≤ ∑ i, y i * y' i := by
  have h := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (y i - 2 * x i + y' i)
  have e : ∑ i, (y i - 2 * x i + y' i) ^ 2 = ∑ i, y i ^ 2 + 4 * ∑ i, x i ^ 2 + ∑ i, y' i ^ 2
      - 4 * ∑ i, y i * x i - 4 * ∑ i, y' i * x i + 2 * ∑ i, y i * y' i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- The squared norm of a sum of unit vectors is the family size plus the inner products
over ordered pairs. -/
theorem sum_sq_sum_eq {ι J : Type} [Fintype ι] [DecidableEq J] (s : Finset J)
    (y : J → ι → ℝ) (hy : ∀ j ∈ s, ∑ i, y j i ^ 2 = 1) :
    ∑ i, (∑ j ∈ s, y j i) ^ 2 = s.card + ∑ j ∈ s, ∑ j' ∈ s.erase j, ∑ i, y j i * y j' i := by
  calc ∑ i, (∑ j ∈ s, y j i) ^ 2 = ∑ j ∈ s, ∑ j' ∈ s, ∑ i, y j i * y j' i := by
        simp_rw [sq, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j ∈ s, (1 + ∑ j' ∈ s.erase j, ∑ i, y j i * y j' i) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.add_sum_erase _ _ hj, ← hy j hj]
        simp only [sq]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- **Star inequality.** If `n` unit vectors each have inner product at least `κ ≥ 0` with a
unit vector, the sum of their inner products over ordered pairs is at least `n² κ² - n`. -/
theorem sum_inner_ordered_pairs_ge {ι J : Type} [Fintype ι] [DecidableEq J] {x : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (s : Finset J) (y : J → ι → ℝ)
    (hy : ∀ j ∈ s, ∑ i, y j i ^ 2 = 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hyx : ∀ j ∈ s, κ ≤ ∑ i, y j i * x i) :
    (s.card : ℝ) ^ 2 * κ ^ 2 - s.card ≤
      ∑ j ∈ s, ∑ j' ∈ s.erase j, ∑ i, y j i * y j' i := by
  have hlin : (s.card : ℝ) * κ ≤ ∑ i, (∑ j ∈ s, y j i) * x i := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simpa using Finset.card_nsmul_le_sum s _ κ hyx
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ∑ j ∈ s, y j i) x
  rw [hx, mul_one, sum_sq_sum_eq s y hy] at hcs
  have h0 : 0 ≤ (s.card : ℝ) * κ := by positivity
  nlinarith

/-! ### The crossing ratio on `[1/2, 1]` -/

/-- On `[1/2, 1]`, the crossing ratio `y = tanHalf x` is nonnegative, inverts as
`x = (1 - y²) / (1 + y²)`, and has `y² ≤ 1/3`. -/
theorem tanHalf_facts {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) :
    0 ≤ tanHalf x ∧ (1 + tanHalf x ^ 2) * x = 1 - tanHalf x ^ 2 ∧ tanHalf x ^ 2 ≤ 1 / 3 := by
  have hsq : tanHalf x ^ 2 = (1 - x) / (1 + x) := by
    rw [tanHalf, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  refine ⟨div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_, ?_⟩
  · rw [hsq]; field_simp; ring
  · rw [hsq, div_le_iff₀ (by linarith)]; linarith

/-- **Tangent bound.** On `[1/2, 1]`, the crossing ratio lies below its tangent line at
`x₀`, scaled by `4 tanHalf x₀` so that the bound survives `x₀ = 1`. -/
theorem tanHalf_tangent {x x₀ : ℝ} (hx : 1 / 2 ≤ x ∧ x ≤ 1) (hx₀ : 1 / 2 ≤ x₀ ∧ x₀ ≤ 1) :
    4 * tanHalf x₀ * tanHalf x ≤ 4 * tanHalf x₀ ^ 2 - (1 + tanHalf x₀ ^ 2) ^ 2 * (x - x₀) := by
  obtain ⟨hy, hxy, hy3⟩ := tanHalf_facts hx.1 hx.2
  obtain ⟨hy₀, hxy₀, hy₀3⟩ := tanHalf_facts hx₀.1 hx₀.2
  set y := tanHalf x
  set y₀ := tanHalf x₀
  have key : (1 + y ^ 2) * (4 * y₀ ^ 2 - (1 + y₀ ^ 2) ^ 2 * (x - x₀) - 4 * y₀ * y) =
      2 * (y - y₀) ^ 2 * (1 - y₀ ^ 2 - 2 * y₀ * y) := by
    linear_combination (-(1 + y₀ ^ 2) ^ 2) * hxy + ((1 + y ^ 2) * (1 + y₀ ^ 2)) * hxy₀
  have hc : 0 ≤ 1 - y₀ ^ 2 - 2 * y₀ * y := by nlinarith [sq_nonneg (y - y₀)]
  have h : 0 ≤ (1 + y ^ 2) * (4 * y₀ ^ 2 - (1 + y₀ ^ 2) ^ 2 * (x - x₀) - 4 * y₀ * y) := by
    rw [key]; exact mul_nonneg (by positivity) hc
  have := nonneg_of_mul_nonneg_right h (by positivity)
  linarith

/-- A finite family of arguments in `[1/2, 1]` with average at least `x₀ ∈ [1/2, 1]` has
`tanHalf`-sum at most the family size times `tanHalf x₀`. -/
theorem sum_tanHalf_le {J : Type} (s : Finset J) (x : J → ℝ) {x₀ : ℝ}
    (hx₀ : 1 / 2 ≤ x₀) (hx₀1 : x₀ ≤ 1) (hx : ∀ j ∈ s, 1 / 2 ≤ x j ∧ x j ≤ 1)
    (hsum : s.card * x₀ ≤ ∑ j ∈ s, x j) :
    ∑ j ∈ s, tanHalf (x j) ≤ s.card * tanHalf x₀ := by
  obtain ⟨hy₀, hxy₀, -⟩ := tanHalf_facts hx₀ hx₀1
  rcases hy₀.lt_or_eq with hpos | hzero
  · have h := Finset.sum_le_sum fun j hj => tanHalf_tangent (hx j hj) ⟨hx₀, hx₀1⟩
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
    have hc : 0 ≤ (1 + tanHalf x₀ ^ 2) ^ 2 * (∑ j ∈ s, x j - s.card * x₀) :=
      mul_nonneg (by positivity) (by linarith)
    have : 4 * tanHalf x₀ * ∑ j ∈ s, tanHalf (x j) ≤ 4 * tanHalf x₀ * (s.card * tanHalf x₀) := by
      linarith
    exact le_of_mul_le_mul_left this (by positivity)
  · -- `tanHalf x₀ = 0` forces `x₀ = 1`, and then every argument is `1`.
    rw [← hzero] at hxy₀
    have hx₀' : x₀ = 1 := by linarith
    subst hx₀'
    have h1 : ∀ j ∈ s, 1 - x j = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun j hj => by linarith [(hx j hj).2]).1 ?_
      refine le_antisymm ?_ (Finset.sum_nonneg fun j hj => by linarith [(hx j hj).2])
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      linarith
    rw [← hzero, mul_zero]
    refine (Finset.sum_eq_zero fun j hj => ?_).le
    rw [show x j = 1 by linarith [h1 j hj], hzero]

/-! ### Stars of three -/

/-- **Crossing ratios in a star of three.** Three unit vectors with inner product at least
`κ ≥ 7/8` with a unit vector have `tanHalf`-sum over the six ordered pairs at most
`6 tanHalf ((3 κ² - 1) / 2)`. -/
theorem sum_tanHalf_star_le {ι J : Type} [Fintype ι] [DecidableEq J] {x : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (s : Finset J) (hs : s.card = 3) (y : J → ι → ℝ)
    (hy : ∀ j ∈ s, ∑ i, y j i ^ 2 = 1) {κ : ℝ} (hκ : 7 / 8 ≤ κ)
    (hyx : ∀ j ∈ s, κ ≤ ∑ i, y j i * x i) :
    ∑ j ∈ s, ∑ j' ∈ s.erase j, tanHalf (∑ i, y j i * y j' i) ≤
      6 * tanHalf ((3 * κ ^ 2 - 1) / 2) := by
  obtain ⟨j₀, hj₀⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have hκ1 : κ ≤ 1 := (hyx j₀ hj₀).trans (inner_le_one (hy j₀ hj₀) hx)
  -- The ordered pairs of distinct members of `s`.
  set P := s.sigma fun j => s.erase j
  have hP : (P.card : ℝ) = 6 := by
    rw [Finset.card_sigma, Finset.sum_congr rfl fun j hj => Finset.card_erase_of_mem hj, hs]
    simp [hs]
  have hpair : ∀ p ∈ P, 1 / 2 ≤ ∑ i, y p.1 i * y p.2 i ∧ ∑ i, y p.1 i * y p.2 i ≤ 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.1 hp
    have h2' := Finset.mem_of_mem_erase h2
    refine ⟨?_, inner_le_one (hy _ h1) (hy _ h2')⟩
    have := le_inner_of_le_inner hx (hy _ h1) (hy _ h2') (hyx _ h1) (hyx _ h2')
    linarith
  have hsum := sum_inner_ordered_pairs_ge hx s y hy (by linarith) hyx
  rw [hs, ← Finset.sum_sigma s (fun j => s.erase j) fun p => ∑ i, y p.1 i * y p.2 i] at hsum
  have h := sum_tanHalf_le P (fun p => ∑ i, y p.1 i * y p.2 i) (x₀ := (3 * κ ^ 2 - 1) / 2)
    (by nlinarith) (by nlinarith) hpair (by rw [hP]; push_cast at hsum; linarith)
  rw [hP, Finset.sum_sigma] at h
  exact h

end Algebraic.Cutwidth.Gaussian.Internal
