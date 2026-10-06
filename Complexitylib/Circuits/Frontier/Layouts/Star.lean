/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Angles in a star

Vectors are functions `ι → ℝ` with the dot product `∑ i, y i * x i`, and the angle between two
unit vectors is the `arccos` of their inner product. A *star* is a family of unit vectors `y j`
each having inner product at least `κ` with a common unit vector `x`. The members of a star are
close to each other:

* `le_inner_of_le_inner`: two of them have inner product at least `4κ - 3`, by expanding
  `‖y - 2x + y'‖ ^ 2 ≥ 0`.
* `sum_inner_ordered_pairs_ge`: if there are `n` of them and `κ ≥ 0`, their inner products over
  ordered pairs sum to at least `n ^ 2 κ ^ 2 - n`. Indeed their sum `S` has squared norm `n`
  plus that sum, and `‖S‖ ≥ ⟨S, x⟩ ≥ n κ` by Cauchy-Schwarz.

Angles are then bounded by concavity:

* `sum_arccos_le`: `arccos` is antitone, and concave on `[0, 1]` since its derivative
  `-1 / √(1 - x ^ 2)` is antitone there. By Jensen's inequality, a family of arguments in
  `[0, 1]` with average at least `x₀` has `arccos`-sum at most the family size times `arccos x₀`.
* `sum_arccos_star_le`: in a star of three with `κ ≥ 7/8`, the six ordered-pair inner products
  lie in `[4κ - 3, 1] ⊆ [0, 1]` and sum to at least `9 κ ^ 2 - 3`, so the six angles sum to at
  most `6 arccos ((3 κ ^ 2 - 1) / 2)`.
-/

@[expose] public section

namespace Complexity.Frontier.Gaussian

/-! ### Inner products in a star -/

/-- Cauchy-Schwarz for unit vectors: their inner product is at most one. -/
private theorem inner_le_one {ι : Type} [Fintype ι] {y y' : ι → ℝ}
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

/-- The squared norm of a sum of unit vectors is the family size plus the inner products over
ordered pairs. -/
private theorem sum_sq_sum_eq {ι J : Type} [Fintype ι] [DecidableEq J] (s : Finset J)
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
unit vector, the sum of their inner products over ordered pairs is at least `n ^ 2 κ ^ 2 - n`. -/
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

/-! ### Angles in a star -/

/-- `arccos` is concave on `[0, 1]`. -/
private theorem concaveOn_arccos : ConcaveOn ℝ (Set.Icc 0 1) Real.arccos := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1) Real.continuous_arccos.continuousOn
    ?_ ?_ <;> rw [interior_Icc]
  · intro x hx
    exact (Real.differentiableAt_arccos.2
      ⟨(by linarith [hx.1] : (-1 : ℝ) < x).ne', hx.2.ne⟩).differentiableWithinAt
  · intro a ha b hb hab
    rw [Real.deriv_arccos]
    have hb' : 0 < 1 - b ^ 2 := by nlinarith [hb.1, hb.2]
    exact neg_le_neg (one_div_le_one_div_of_le (Real.sqrt_pos.2 hb')
      (Real.sqrt_le_sqrt (by nlinarith [ha.1])))

/-- **Concavity bound for `arccos`.** `arccos` is concave on `[0, 1]` and antitone, so a finite
family of arguments in that interval with average at least `x₀` has `arccos`-sum at most the
family size times `arccos x₀`. -/
theorem sum_arccos_le {J : Type} (s : Finset J) (x : J → ℝ) {x₀ : ℝ}
    (hx : ∀ j ∈ s, 0 ≤ x j ∧ x j ≤ 1) (hsum : s.card * x₀ ≤ ∑ j ∈ s, x j) :
    ∑ j ∈ s, Real.arccos (x j) ≤ s.card * Real.arccos x₀ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hne.card_pos
  have h := concaveOn_arccos.le_map_sum (t := s) (w := fun _ => (s.card : ℝ)⁻¹) (p := x)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hn.ne'])
    hx
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have hmono : Real.arccos ((s.card : ℝ)⁻¹ * ∑ j ∈ s, x j) ≤ Real.arccos x₀ :=
    Real.arccos_le_arccos ((le_inv_mul_iff₀ hn).2 hsum)
  exact (inv_mul_le_iff₀ hn).1 (h.trans hmono)

/-- **Angles in a star of three.** Three unit vectors with inner product at least `κ ≥ 7/8`
with a unit vector have pairwise angles summing, over the six ordered pairs, to at most
`6 arccos ((3 κ ^ 2 - 1) / 2)`. -/
theorem sum_arccos_star_le {ι J : Type} [Fintype ι] [DecidableEq J] {x : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (s : Finset J) (hs : s.card = 3) (y : J → ι → ℝ)
    (hy : ∀ j ∈ s, ∑ i, y j i ^ 2 = 1) {κ : ℝ} (hκ : 7 / 8 ≤ κ)
    (hyx : ∀ j ∈ s, κ ≤ ∑ i, y j i * x i) :
    ∑ j ∈ s, ∑ j' ∈ s.erase j, Real.arccos (∑ i, y j i * y j' i) ≤
      6 * Real.arccos ((3 * κ ^ 2 - 1) / 2) := by
  -- The ordered pairs of distinct members of `s`.
  set P := s.sigma fun j => s.erase j
  have hP : (P.card : ℝ) = 6 := by
    rw [Finset.card_sigma, Finset.sum_congr rfl fun j hj => Finset.card_erase_of_mem hj, hs]
    simp [hs]
  have hpair : ∀ p ∈ P, 0 ≤ ∑ i, y p.1 i * y p.2 i ∧ ∑ i, y p.1 i * y p.2 i ≤ 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_sigma.1 hp
    have h2' := Finset.mem_of_mem_erase h2
    refine ⟨?_, inner_le_one (hy _ h1) (hy _ h2')⟩
    have := le_inner_of_le_inner hx (hy _ h1) (hy _ h2') (hyx _ h1) (hyx _ h2')
    linarith
  have hsum := sum_inner_ordered_pairs_ge hx s y hy (by linarith) hyx
  rw [hs, ← Finset.sum_sigma s (fun j => s.erase j) fun p => ∑ i, y p.1 i * y p.2 i] at hsum
  have h := sum_arccos_le P (fun p => ∑ i, y p.1 i * y p.2 i) (x₀ := (3 * κ ^ 2 - 1) / 2)
    hpair (by rw [hP]; push_cast at hsum; linarith)
  rwa [hP, Finset.sum_sigma] at h

end Complexity.Frontier.Gaussian
