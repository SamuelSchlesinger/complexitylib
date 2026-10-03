/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Suppression
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryNormalization
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Reduction
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Clusters.Density.Internal

/-!
# Uniformly bounded helpful sets and sharp cubic bisections

The finite red-density theorem supplies a positive set in every normalized
side whose cut density exceeds `1/3` by a fixed positive amount. Suppression
lifts it with a factor four, and reversing boundary normalization costs a
factor three. The uniform helpful-set bound then gives the asymptotic cubic
bisection theorem through the existing accumulation and rebalancing reduction.

Source: Burkhard Monien and Robert Preis, *Upper bounds on the bisection
width of 3- and 4-regular graphs*, Journal of Discrete Algorithms 4 (2006),
475–498, https://doi.org/10.1016/j.jda.2005.12.009.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem exists_normalized_helpful_of_density {S : Finset W}
    (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {ξ : ℝ} (hξ : 0 < ξ) (M : ℕ) (positive : 0 < M)
    (budget : 4 ≤ 3 * ξ * M)
    (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) :
    ∃ X ⊆ S, X.card ≤ 12 * M * (1 + 3 * M) ∧ 1 ≤ helpfulness H S X := by
  obtain ⟨Q⟩ := Bisection.exists_boundarySuppression H regular outside independent
  have redDensity :
      (1 / 2 + 3 * ξ / 2) * Fintype.card {v : W // v ∈ S \ cutBoundary H S} <
        Fintype.card {c : W // c ∈ cutBoundary H S} := by
    simpa only [Fintype.card_coe] using Bisection.boundary_red_density H hξ outside dense
  have redBudget : (2 : ℝ) ≤ (3 * ξ / 2) * M := by nlinarith only [budget]
  obtain ⟨X, size, gain⟩ := RedBlack.Internal.exists_positive_of_red_density
    (H.induce {v | v ∈ S \ cutBoundary H S}) Q.red Q.loopless
      (Q.degree_sum regular) M positive redBudget redDensity
  obtain ⟨Y, inside, liftedSize, helpful⟩ :=
    Q.exists_helpful_set_of_positive regular outside independent gain
  refine ⟨Y, inside, ?_, helpful⟩
  calc
    Y.card ≤ 4 * X.card := liftedSize
    _ ≤ 4 * (3 * M * (1 + 3 * M)) := Nat.mul_le_mul_left 4 size
    _ = 12 * M * (1 + 3 * M) := by ring

theorem exists_bounded_helpful (regular : H.IsRegularOfDegree 3)
    {ξ : ℝ} (hξ : 0 < ξ) (M : ℕ) (positive : 0 < M) (budget : 4 ≤ 3 * ξ * M)
    {S : Finset W} (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) :
    ∃ X ⊆ S, X.card ≤ 36 * M * (1 + 3 * M) ∧ 1 ≤ helpfulness H S X := by
  obtain small | ⟨G, regularG, cut, _, outside, independent, transfer⟩ :=
    Bisection.exists_independent_boundary_or_small_helpful H S regular
  · obtain ⟨X, inside, size, helpful⟩ := small
    refine ⟨X, inside, size.trans ?_, helpful⟩
    calc
      33 ≤ 36 * M := by lia
      _ ≤ 36 * M * (1 + 3 * M) := by rw [Nat.mul_add, Nat.mul_one]; lia
  · have denseG : (1 / 3 + ξ) * S.card < (G.cutFinset S).card := by
      simpa only [cut] using dense
    obtain ⟨X, inside, size, helpful⟩ :=
      exists_normalized_helpful_of_density G regularG outside independent hξ M positive budget
        denseG
    obtain ⟨Y, insideY, _, sizeY, helpfulY⟩ := transfer X inside
    refine ⟨Y, insideY, ?_, helpful.trans helpfulY⟩
    calc
      Y.card ≤ 3 * X.card := sizeY
      _ ≤ 3 * (12 * M * (1 + 3 * M)) := Nat.mul_le_mul_left 3 size
      _ = 36 * M * (1 + 3 * M) := by ring

theorem exists_bisectionBound {ξ : ℝ} (hξ : 0 < ξ) : ∃ N₀ : ℕ, BisectionBound ξ N₀ := by
  obtain ⟨M, large⟩ := exists_nat_gt (4 / (3 * ξ))
  have denominator : (0 : ℝ) < 3 * ξ := by positivity
  have positive : 0 < M := by
    have positiveReal : (0 : ℝ) < M := (div_pos (by norm_num) denominator).trans large
    exact_mod_cast positiveReal
  have budget : (4 : ℝ) ≤ 3 * ξ * M := by
    have scaled := (div_lt_iff₀ denominator).mp large
    nlinarith only [scaled]
  apply Bisection.exists_bisectionBound_of_helpful hξ (36 * M * (1 + 3 * M))
  intro V _ _ B _ regular S dense
  exact exists_bounded_helpful B
    (fun v => by simpa only [← SimpleGraph.ncard_neighborSet] using regular.degree_eq v)
    hξ M positive budget dense

end Algebraic.Cutwidth.Bisection.Internal
