/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryNormalization.Internal

/-!
# The first normalization phase with a uniform reverse bound

This completes Monien and Preis's elimination of edges between boundary
vertices. Either a helpful set of at most 33 vertices already exists, or
there is a cubic graph on the same vertices with the same cut and boundary,
independent boundary vertices, and one outside edge per boundary vertex.
Every moved set in that graph transfers back with no loss of helpfulness
and at most a factor-three increase in size.

The original boundary edges form a matching after small helpful sets have
been excluded. Reversing a switch adds at most two vertices and completes
one of these pairs. The selected boundary vertices stay within the original
pair closure of the initial selection, which has at most twice its size.
This controls the whole sequence independently of its length.

`NeighborNormalization` completes the second phase, eliminating interior
vertices with three boundary neighbors and supplying its own reverse bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

/-- Either a uniformly small helpful set exists, or boundary-edge elimination
produces an independent boundary and a factor-three transfer of all moved sets. -/
theorem exists_independent_boundary_or_small_helpful {W : Type} [Fintype W]
    (H : SimpleGraph W) (S : Finset W) (regular : H.IsRegularOfDegree 3) :
    (∃ X ⊆ S, X.card ≤ 33 ∧ 1 ≤ helpfulness H S X) ∨
      ∃ G : SimpleGraph W, G.IsRegularOfDegree 3 ∧ G.cutFinset S = H.cutFinset S ∧
        cutBoundary G S = cutBoundary H S ∧
        (∀ c ∈ cutBoundary G S, (G.neighborFinset c \ S).card = 1) ∧
        (∀ a ∈ cutBoundary G S, ∀ b ∈ cutBoundary G S, ¬ G.Adj a b) ∧
        ∀ X ⊆ S, ∃ Y ⊆ S, X ⊆ Y ∧ Y.card ≤ 3 * X.card ∧
          helpfulness G S X ≤ helpfulness H S Y :=
  BoundaryNormalization.Internal.exists_independent_boundary_or_small_helpful H S regular

end Algebraic.Cutwidth.Bisection
