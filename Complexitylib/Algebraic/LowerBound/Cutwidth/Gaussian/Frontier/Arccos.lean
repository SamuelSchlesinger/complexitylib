/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Arccos.Internal

/-!
# Angles in a star

Vectors are functions `ι → ℝ` with the dot product `∑ i, y i * x i`. For unit vectors the
angle between them is `arccos` of their inner product. When unit vectors `y j` all have inner
product at least `κ` with a common unit vector `x`, the angles over their ordered pairs are
controlled by `κ`, exactly as the crossing ratios are in
`Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star`.

* `sum_arccos_le`: `arccos` is concave on `[0, 1]` and antitone, so a family of arguments
  there with average at least `x₀` has `arccos`-sum at most the family size times
  `arccos x₀`.
* `sum_arccos_star_le`: for three vectors and `κ ≥ 7/8`, the six ordered-pair angles sum to
  at most `6 arccos ((3 κ² - 1) / 2)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- **Concavity bound for `arccos`.** `arccos` is concave on `[0, 1]` and antitone, so a
finite family of arguments in that interval with average at least `x₀` has `arccos`-sum at
most the family size times `arccos x₀`. -/
theorem sum_arccos_le {J : Type} (s : Finset J) (x : J → ℝ) {x₀ : ℝ}
    (hx : ∀ j ∈ s, 0 ≤ x j ∧ x j ≤ 1) (hsum : s.card * x₀ ≤ ∑ j ∈ s, x j) :
    ∑ j ∈ s, Real.arccos (x j) ≤ s.card * Real.arccos x₀ :=
  Internal.sum_arccos_le s x hx hsum

/-- **Angles in a star of three.** Three unit vectors with inner product at least
`κ ≥ 7/8` with a unit vector have pairwise angles summing, over the six ordered pairs, to
at most `6 arccos ((3 κ² - 1) / 2)`. -/
theorem sum_arccos_star_le {ι J : Type} [Fintype ι] [DecidableEq J] {x : ι → ℝ}
    (hx : ∑ i, x i ^ 2 = 1) (s : Finset J) (hs : s.card = 3) (y : J → ι → ℝ)
    (hy : ∀ j ∈ s, ∑ i, y j i ^ 2 = 1) {κ : ℝ} (hκ : 7 / 8 ≤ κ)
    (hyx : ∀ j ∈ s, κ ≤ ∑ i, y j i * x i) :
    ∑ j ∈ s, ∑ j' ∈ s.erase j, Real.arccos (∑ i, y j i * y j' i) ≤
      6 * Real.arccos ((3 * κ ^ 2 - 1) / 2) :=
  Internal.sum_arccos_star_le hx s hs y hy hκ hyx

end Algebraic.Cutwidth.Gaussian
