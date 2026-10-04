/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Helpful.Internal

/-!
# Sharp asymptotic bisections of cubic graphs

Every positive slack admits a uniform bound on the size of a helpful set.
The connected-cluster red-density argument supplies the normalized witness;
boundary lifting and reversing normalization increase its size by factors
four and three. Accumulation and rebalancing then prove the sharp cubic
bisection bound, and the Fomin–Høie reduction gives the pathwidth bound.

The bisection conclusion is due to Burkhard Monien and Robert Preis,
*Upper bounds on the bisection width of 3- and 4-regular graphs*, Journal of
Discrete Algorithms 4 (2006), 475–498, https://doi.org/10.1016/j.jda.2005.12.009.
The connected-cluster replacement for their red/black reorganization is a
deduction developed in this formalization.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

namespace Bisection

/-- A normalized cubic side above density `1/3 + ξ` has a bounded helpful
set. The parameter `M` depends only on the density slack. -/
theorem exists_normalized_helpful_of_density {W : Type} [Fintype W] (H : SimpleGraph W)
    {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {ξ : ℝ} (hξ : 0 < ξ) (M : ℕ) (positive : 0 < M)
    (budget : 4 ≤ 3 * ξ * M)
    (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) :
    ∃ X ⊆ S, X.card ≤ 12 * M * (1 + 3 * M) ∧ 1 ≤ helpfulness H S X :=
  Internal.exists_normalized_helpful_of_density H regular outside independent
    hξ M positive budget dense

/-- Every cubic side above density `1/3 + ξ` has a helpful set whose size
is bounded independently of the graph and of the side. -/
theorem exists_bounded_helpful {W : Type} [Fintype W] (H : SimpleGraph W)
    (regular : H.IsRegularOfDegree 3) {ξ : ℝ} (hξ : 0 < ξ)
    (M : ℕ) (positive : 0 < M) (budget : 4 ≤ 3 * ξ * M)
    {S : Finset W} (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) :
    ∃ X ⊆ S, X.card ≤ 36 * M * (1 + 3 * M) ∧ 1 ≤ helpfulness H S X :=
  Internal.exists_bounded_helpful H regular hξ M positive budget dense

/-- **The Monien–Preis cubic bisection bound.** For every positive slack,
every sufficiently large simple cubic graph has a balanced cut with at most
`(1/6 + ξ) n` crossing edges. -/
theorem exists_bisectionBound {ξ : ℝ} (hξ : 0 < ξ) : ∃ N₀ : ℕ, BisectionBound ξ N₀ :=
  Internal.exists_bisectionBound hξ

end Bisection

/-- **The Fomin–Høie cubic pathwidth bound.** Every positive slack admits
the corresponding asymptotic bound, with coefficient `1/6`, for simple cubic
graphs. -/
theorem exists_pathwidthBound {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, PathwidthBound (1 / 6) ξ N₀ :=
  pathwidthBound_of_bisectionBound (fun _ h => Bisection.exists_bisectionBound h) ξ hξ

end Algebraic.Cutwidth
