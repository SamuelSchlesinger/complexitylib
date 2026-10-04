/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Internal

/-!
# Inner products in a star

Vectors are functions `ι → ℝ` with the dot product `∑ i, y i * x i`. When unit vectors
`y j` all have inner product at least `κ` with a common unit vector `x`, they are close to
each other.

* `le_inner_of_le_inner`: two such vectors have inner product at least `4κ - 3`.
* `sum_inner_ordered_pairs_ge`: for `n` such vectors and `κ ≥ 0`, the inner products over
  ordered pairs sum to at least `n² κ² - n`, since the sum of the vectors has squared norm
  at least `(n κ)²` by Cauchy–Schwarz.

`Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Arccos` turns these bounds
into a bound on the pairwise angles.
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

end Algebraic.Cutwidth.Gaussian
