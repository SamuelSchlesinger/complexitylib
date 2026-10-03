/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.LocalConfigurations.Internal

/-!
# Helpful configurations used in normalization

Monien and Preis's *Upper Bounds on the Bisection Width of 3- and 4-regular
Graphs* excludes five local configurations before normalizing the graph.
`Improvement` covers the singleton and connected-boundary cases. This module
proves the remaining witnesses of at most five, seven, and eleven vertices.
All statements allow a subcubic graph and overlapping boundary neighborhoods.

The eleven-vertex construction starts with a nonnegative-helpfulness set
of at most four vertices, then closes a small interior set under its neighbors.
Its contrapositive supplies the interior neighbor of boundary degree at most
one needed for an edge switch. `EdgeSwitch` proves one switch and its local
reverse transfer. `BoundaryNormalization` and `NeighborNormalization` complete
both phases with a uniform bound on their combined reverse extension.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- Adding a vertex contributes its singleton helpfulness and twice the
number of its neighbors already in the moved set. -/
theorem helpfulness_insert {S X : Finset W} (hX : X ⊆ S) {v : W}
    (hv : v ∈ S) (fresh : v ∉ X) :
    helpfulness H S (insert v X) = helpfulness H S X +
      2 * ((H.neighborFinset v \ S).card : ℤ) - H.degree v +
      2 * ((H.neighborFinset v ∩ X).card : ℤ) :=
  Bisection.Internal.helpfulness_insert H hX hv fresh

namespace Bisection

/-- Each new boundary vertex attached to the old set increases helpfulness
by at least one. -/
theorem helpfulness_union_boundary {S X A : Finset W}
    (hX : X ⊆ S) (hA : A ⊆ cutBoundary H S)
    (degree : ∀ c ∈ A, H.degree c ≤ 3)
    (adjacent : ∀ c ∈ A, ∃ x ∈ X, H.Adj c x) :
    helpfulness H S X + (A \ X).card ≤ helpfulness H S (X ∪ A) :=
  Internal.helpfulness_union_boundary H hX hA degree adjacent

/-- Adjoining an interior set and its boundary neighbors improves helpfulness
if the interior set has no other neighbors and has an edge to the old set. -/
theorem helpfulness_union_boundaryLift_of_closed {S X Z : Finset W}
    (hX : X ⊆ S) (hZ : Z ⊆ S \ cutBoundary H S)
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (closed : ∀ z ∈ Z, H.neighborFinset z ⊆ (X ∪ Z) ∪ cutBoundary H S)
    (touch : ∃ x ∈ X, ∃ z ∈ Z \ X, H.Adj x z) :
    helpfulness H S X + 1 ≤ helpfulness H S (X ∪ boundaryLift H S Z) :=
  Internal.helpfulness_union_boundaryLift_of_closed H hX hZ degree closed touch

/-- Adjacent boundary vertices form a set of nonnegative helpfulness. -/
theorem nonneg_helpfulness_boundary_pair {S : Finset W} {c d : W}
    (hc : c ∈ cutBoundary H S) (hd : d ∈ cutBoundary H S)
    (degree : ∀ v ∈ S, H.degree v ≤ 3) (adjacent : H.Adj c d) :
    0 ≤ helpfulness H S {c, d} :=
  Internal.nonneg_helpfulness_boundary_pair H hc hd degree adjacent

/-- A vertex with three boundary neighbors and those neighbors form a set
of nonnegative helpfulness. -/
theorem nonneg_helpfulness_boundary_star {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v : W} (hv : v ∈ S)
    (three : (H.neighborFinset v ∩ cutBoundary H S).card = 3) :
    0 ≤ helpfulness H S (insert v (H.neighborFinset v ∩ cutBoundary H S)) :=
  Internal.nonneg_helpfulness_boundary_star H degree hv three

/-- Monien--Preis configuration (iii): a boundary edge incident to the
neighborhood of an interior vertex with three boundary neighbors. -/
theorem exists_helpful_of_boundary_pair_three_neighbors {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {c d v : W}
    (hc : c ∈ cutBoundary H S) (hd : d ∈ cutBoundary H S) (pair : H.Adj c d)
    (hv : v ∈ S \ cutBoundary H S) (adjacent : H.Adj v c)
    (three : (H.neighborFinset v ∩ cutBoundary H S).card = 3) :
    ∃ X ⊆ S, X.card ≤ 5 ∧ 1 ≤ helpfulness H S X :=
  Internal.exists_helpful_of_boundary_pair_three_neighbors H degree hc hd pair hv adjacent three

/-- Monien--Preis configuration (iv): two interior vertices with three
boundary neighbors share one of those neighbors. -/
theorem exists_helpful_of_shared_boundary_neighbor {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {u v c : W}
    (hu : u ∈ S \ cutBoundary H S) (hv : v ∈ S \ cutBoundary H S) (distinct : u ≠ v)
    (hc : c ∈ cutBoundary H S) (adjU : H.Adj u c) (adjV : H.Adj v c)
    (threeU : (H.neighborFinset u ∩ cutBoundary H S).card = 3)
    (threeV : (H.neighborFinset v ∩ cutBoundary H S).card = 3) :
    ∃ X ⊆ S, X.card ≤ 7 ∧ 1 ≤ helpfulness H S X :=
  Internal.exists_helpful_of_shared_boundary_neighbor H degree hu hv distinct hc
    adjU adjV threeU threeV

/-- A nonnegative-helpfulness set grows into a helpful set using at most
seven new vertices if each remaining neighbor of an adjacent interior vertex
is a boundary vertex or has at least two boundary neighbors. -/
theorem exists_helpful_extension_of_neighbor_types {S X : Finset W}
    (hX : X ⊆ S) (neutral : 0 ≤ helpfulness H S X)
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v : W}
    (hv : v ∈ S \ cutBoundary H S) (fresh : v ∉ X)
    (touch : ∃ x ∈ X, H.Adj v x)
    (neighbors : ∀ p, H.Adj v p → p ∉ X → p ∈ cutBoundary H S ∨
      (p ∈ S \ cutBoundary H S ∧ 2 ≤ (H.neighborFinset p ∩ cutBoundary H S).card)) :
    ∃ Y ⊆ S, Y.card ≤ X.card + 7 ∧ 1 ≤ helpfulness H S Y :=
  Internal.exists_helpful_extension_of_neighbor_types H hX neutral degree hv fresh touch neighbors

/-- Monien--Preis configuration (v), covering either a boundary edge or a
vertex with three boundary neighbors at the other end of the boundary attachment. -/
theorem exists_helpful_of_boundary_neighbor_configuration {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v c : W}
    (hv : v ∈ S \ cutBoundary H S) (hc : c ∈ cutBoundary H S) (adjacent : H.Adj v c)
    (anchor : (∃ d ∈ cutBoundary H S, H.Adj c d) ∨
      ∃ u ∈ S \ cutBoundary H S, u ≠ v ∧ H.Adj c u ∧
        (H.neighborFinset u ∩ cutBoundary H S).card = 3)
    (neighbors : ∀ p, H.Adj v p → p ≠ c → p ∈ cutBoundary H S ∨
      (p ∈ S \ cutBoundary H S ∧ 2 ≤ (H.neighborFinset p ∩ cutBoundary H S).card)) :
    ∃ Y ⊆ S, Y.card ≤ 11 ∧ 1 ≤ helpfulness H S Y :=
  Internal.exists_helpful_of_boundary_neighbor_configuration H degree hv hc adjacent anchor neighbors

/-- If no helpful set of at most eleven vertices exists, the edge-switch
configuration has another interior neighbor with at most one boundary neighbor. -/
theorem exists_switch_neighbor {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0) {v c : W}
    (hv : v ∈ S \ cutBoundary H S) (hc : c ∈ cutBoundary H S) (adjacent : H.Adj v c)
    (anchor : (∃ d ∈ cutBoundary H S, H.Adj c d) ∨
      ∃ u ∈ S \ cutBoundary H S, u ≠ v ∧ H.Adj c u ∧
        (H.neighborFinset u ∩ cutBoundary H S).card = 3) :
    ∃ p, H.Adj v p ∧ p ≠ c ∧ p ∈ S \ cutBoundary H S ∧
      (H.neighborFinset p ∩ cutBoundary H S).card ≤ 1 :=
  Internal.exists_switch_neighbor H degree noHelpful hv hc adjacent anchor

/-- Excluding the singleton helpful case leaves one outside edge at every
boundary vertex. -/
theorem outside_eq_one_of_no_small_helpful {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {c : W} (hc : c ∈ cutBoundary H S) : (H.neighborFinset c \ S).card = 1 :=
  Internal.outside_eq_one_of_no_small_helpful H degree noHelpful hc

/-- Excluding three connected boundary vertices leaves maximum degree one
in the boundary-induced graph. -/
theorem boundary_degree_le_one_of_no_small_helpful {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {c : W} (hc : c ∈ cutBoundary H S) :
    (H.neighborFinset c ∩ cutBoundary H S).card ≤ 1 :=
  Internal.boundary_degree_le_one_of_no_small_helpful H degree noHelpful hc

end Bisection

end Algebraic.Cutwidth
