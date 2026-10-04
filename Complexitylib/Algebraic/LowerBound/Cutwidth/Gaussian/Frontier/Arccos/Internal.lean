/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Internal
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Angle sums in a star: proofs

Vectors are functions `ι → ℝ` with the dot product `∑ i, y i * x i`.

* `arccos` is concave on `[0, 1]`, since its derivative `-1 / √(1 - x²)` is antitone on
  `(0, 1)`.
* Jensen's inequality with uniform weights on a nonempty family, followed by antitonicity of
  `arccos`, bounds the `arccos`-sum of a family in `[0, 1]` whose arguments average at
  least `x₀`.
* In a star of three, every ordered-pair inner product lies in `[4κ - 3, 1] ⊆ [0, 1]`, and
  the six of them sum to at least `9κ² - 3` by the star inequality.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

/-- `arccos` is concave on `[0, 1]`. -/
theorem concaveOn_arccos : ConcaveOn ℝ (Set.Icc 0 1) Real.arccos := by
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

/-- A finite family of arguments in `[0, 1]` with average at least `x₀` has `arccos`-sum at
most the family size times `arccos x₀`. -/
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
with a unit vector have `arccos`-sum over the six ordered pairs at most
`6 arccos ((3 κ² - 1) / 2)`. -/
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
  rw [hP, Finset.sum_sigma] at h
  exact h

end Algebraic.Cutwidth.Gaussian.Internal
