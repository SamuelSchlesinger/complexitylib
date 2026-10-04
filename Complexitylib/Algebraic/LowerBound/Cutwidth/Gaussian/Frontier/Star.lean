/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Internal

/-!
# Crossing ratios in a star

Vectors are functions `ι → ℝ` with the dot product `∑ i, y i * x i`. When unit vectors
`y j` all have inner product at least `κ` with a common unit vector `x`, they are close to
each other, and the crossing ratios `tanHalf ⟨y j, y j'⟩ = √(1 - ⟨y j, y j'⟩) / √(1 + ⟨y j, y j'⟩)`
over their ordered pairs are controlled by `κ`.

* `le_inner_of_le_inner`: two such vectors have inner product at least `4κ - 3`.
* `sum_inner_ordered_pairs_ge`: for `n` such vectors and `κ ≥ 0`, the inner products over
  ordered pairs sum to at least `n² κ² - n`, since the sum of the vectors has squared norm
  at least `(n κ)²` by Cauchy–Schwarz.
* `sum_tanHalf_le`: `tanHalf` is concave on `[1/2, 1]`, so a family of arguments there with
  average at least `x₀ ∈ [1/2, 1]` has `tanHalf`-sum at most the family size times
  `tanHalf x₀`.
* `sum_tanHalf_star_le`: for three vectors and `κ ≥ 7/8`, the six ordered-pair crossing
  ratios sum to at most `6 tanHalf ((3 κ² - 1) / 2)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- Unit vectors close to a common unit vector are close to each other. -/
theorem le_inner_of_le_inner {ι : Type} [Fintype ι] {x y y' : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) (hy' : ∑ i, y' i ^ 2 = 1) {κ : ℝ}
    (hyx : κ ≤ ∑ i, y i * x i) (hy'x : κ ≤ ∑ i, y' i * x i) :
    4 * κ - 3 ≤ ∑ i, y i * y' i :=
  Internal.le_inner_of_le_inner hx hy hy' hyx hy'x

/-- **Star inequality.** If `n` unit vectors each have inner product at least `κ ≥ 0` with a
unit vector, the sum of their inner products over ordered pairs is at least `n² κ² - n`. -/
theorem sum_inner_ordered_pairs_ge {ι J : Type} [Fintype ι] [DecidableEq J] {x : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (s : Finset J) (y : J → ι → ℝ)
    (hy : ∀ j ∈ s, ∑ i, y j i ^ 2 = 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (hyx : ∀ j ∈ s, κ ≤ ∑ i, y j i * x i) :
    (s.card : ℝ) ^ 2 * κ ^ 2 - s.card ≤
      ∑ j ∈ s, ∑ j' ∈ s.erase j, ∑ i, y j i * y j' i :=
  Internal.sum_inner_ordered_pairs_ge hx s y hy hκ hyx

/-- **Tangent bound.** `tanHalf` is concave on `[1/2, 1]`, so a finite family of arguments
in that interval with average at least `x₀ ∈ [1/2, 1]` has `tanHalf`-sum at most the
family size times `tanHalf x₀`. -/
theorem sum_tanHalf_le {J : Type} (s : Finset J) (x : J → ℝ) {x₀ : ℝ}
    (hx₀ : 1 / 2 ≤ x₀) (hx₀1 : x₀ ≤ 1) (hx : ∀ j ∈ s, 1 / 2 ≤ x j ∧ x j ≤ 1)
    (hsum : s.card * x₀ ≤ ∑ j ∈ s, x j) :
    ∑ j ∈ s, tanHalf (x j) ≤ s.card * tanHalf x₀ :=
  Internal.sum_tanHalf_le s x hx₀ hx₀1 hx hsum

/-- **Crossing ratios in a star of three.** Three unit vectors with inner product at least
`κ ≥ 7/8` with a unit vector have `tanHalf`-sum over the six ordered pairs at most
`6 tanHalf ((3 κ² - 1) / 2)`. -/
theorem sum_tanHalf_star_le {ι J : Type} [Fintype ι] [DecidableEq J] {x : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (s : Finset J) (hs : s.card = 3) (y : J → ι → ℝ)
    (hy : ∀ j ∈ s, ∑ i, y j i ^ 2 = 1) {κ : ℝ} (hκ : 7 / 8 ≤ κ)
    (hyx : ∀ j ∈ s, κ ≤ ∑ i, y j i * x i) :
    ∑ j ∈ s, ∑ j' ∈ s.erase j, tanHalf (∑ i, y j i * y j' i) ≤
      6 * tanHalf ((3 * κ ^ 2 - 1) / 2) :=
  Internal.sum_tanHalf_star_le hx s hs y hy hκ hyx

end Algebraic.Cutwidth.Gaussian
