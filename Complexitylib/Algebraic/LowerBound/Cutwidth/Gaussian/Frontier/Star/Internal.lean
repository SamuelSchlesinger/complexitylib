/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Defs

/-!
# Inner products in a star: proofs

Vectors are functions `ι → ℝ` with the dot product `∑ i, y i * x i`.

* Two unit vectors with inner product at least `κ` with a common unit vector satisfy
  `‖y - y'‖² ≤ 2 ‖y - x‖² + 2 ‖x - y'‖²`, which gives inner product at least `4κ - 3`.
* For the sum `S` of the vectors `y j`, `‖S‖²` is the family size plus the ordered-pair
  inner products, and Cauchy–Schwarz against the unit vector gives `‖S‖² ≥ (n κ)²`.
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

end Algebraic.Cutwidth.Gaussian.Internal
