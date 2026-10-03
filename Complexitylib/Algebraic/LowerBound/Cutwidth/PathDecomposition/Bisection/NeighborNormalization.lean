/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.NeighborNormalization.Internal

/-!
# Complete boundary normalization with a uniform reverse bound

This completes the second phase of Monien and Preis's normalization:
eliminating interior vertices with three boundary neighbors. Starting
with an independent boundary, it gives either a helpful set of at most
55 vertices or a normalized graph whose moved sets transfer back with
at most a factor-five size increase and no loss of helpfulness.

The original three-neighbor stars are disjoint once small helpful sets
are excluded. A switch processes one fresh center. In reverse order,
give a selected boundary vertex of each still-processed star four credits
and its selected center one. Restoring that star spends its own credits,
adds at most four vertices, and selects no earlier center. This potential
telescopes to the factor-five bound independently of the sequence length.

Combining with `BoundaryNormalization` completes both phases for any cubic
graph: either there is a helpful set of at most 165 vertices, or all moved
sets in a normalized graph transfer back with a factor-fifteen bound.
The normalized red/black helpful-set theorem remains a separate obligation.

Source: Burkhard Monien and Robert Preis, *Upper bounds on the bisection
width of 3- and 4-regular graphs*, Journal of Discrete Algorithms 4 (2006),
475–498, https://doi.org/10.1016/j.jda.2005.12.009.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

variable {W : Type} [Fintype W]

/-- With an independent boundary, eliminate all three-boundary-neighbor
vertices or find a helpful set of at most 55 vertices. All moved sets in
the resulting graph transfer back with at most five times their size. -/
theorem exists_no_three_neighbors_or_small_helpful (H : SimpleGraph W) (S : Finset W)
    (regular : H.IsRegularOfDegree 3)
    (independent : ∀ a ∈ cutBoundary H S, ∀ b ∈ cutBoundary H S, ¬ H.Adj a b) :
    (∃ X ⊆ S, X.card ≤ 55 ∧ 1 ≤ helpfulness H S X) ∨
      ∃ G : SimpleGraph W, G.IsRegularOfDegree 3 ∧ G.cutFinset S = H.cutFinset S ∧
        cutBoundary G S = cutBoundary H S ∧
        (∀ c ∈ cutBoundary G S, (G.neighborFinset c \ S).card = 1) ∧
        (∀ a ∈ cutBoundary G S, ∀ b ∈ cutBoundary G S, ¬ G.Adj a b) ∧
        (∀ v ∈ S \ cutBoundary G S, (G.neighborFinset v ∩ cutBoundary G S).card ≤ 2) ∧
        ∀ X ⊆ S, ∃ Y ⊆ S, X ⊆ Y ∧ Y.card ≤ 5 * X.card ∧
          helpfulness G S X ≤ helpfulness H S Y :=
  NeighborNormalization.Internal.exists_no_three_neighbors_or_small_helpful H S regular independent

/-- Complete both normalization phases in a cubic graph. Either a helpful
set of at most 165 vertices exists, or normalization preserves the cut and
boundary and gives a factor-fifteen reverse transfer for every moved set. -/
theorem exists_normalization_or_small_helpful (H : SimpleGraph W) (S : Finset W)
    (regular : H.IsRegularOfDegree 3) :
    (∃ X ⊆ S, X.card ≤ 165 ∧ 1 ≤ helpfulness H S X) ∨
      ∃ G : SimpleGraph W, G.IsRegularOfDegree 3 ∧ G.cutFinset S = H.cutFinset S ∧
        cutBoundary G S = cutBoundary H S ∧
        (∀ c ∈ cutBoundary G S, (G.neighborFinset c \ S).card = 1) ∧
        (∀ a ∈ cutBoundary G S, ∀ b ∈ cutBoundary G S, ¬ G.Adj a b) ∧
        (∀ v ∈ S \ cutBoundary G S, (G.neighborFinset v ∩ cutBoundary G S).card ≤ 2) ∧
        ∀ X ⊆ S, ∃ Y ⊆ S, X ⊆ Y ∧ Y.card ≤ 15 * X.card ∧
          helpfulness G S X ≤ helpfulness H S Y :=
  NeighborNormalization.Internal.exists_normalization_or_small_helpful H S regular

end Algebraic.Cutwidth.Bisection
