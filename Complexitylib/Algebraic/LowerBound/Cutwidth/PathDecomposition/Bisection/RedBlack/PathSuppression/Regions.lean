/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions.Internal

/-!
# The core forest after path suppression

Connected, disjoint regions separated from one another give distinct
independent vertices in the boundary quotient. When their cuts have size
at most two and cycles avoid them, suppressing these region vertices
produces a forest on the remaining core pieces, with exactly the original
reachability between those pieces.
The number of core edges is exactly the number of regions with two boundary edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression

open scoped Classical

/-- Construct the forest on the pieces outside all regions, suppressing the
region vertices and preserving reachability between representative vertices.
Its edges count exactly the regions with two boundary edges. -/
theorem exists_core_forest {V ι : Type} [Fintype V] [Fintype ι]
    (B : SimpleGraph V) (P : ι → Finset V)
    (connected : ∀ i, (B.induce {v | v ∈ P i}).Connected)
    (disjoint : Pairwise (fun i j => Disjoint (P i) (P j)))
    (separate : ∀ i j, ∀ u ∈ P i, ∀ v ∈ P j, B.Adj u v → i = j)
    (boundary : ∀ i, (B.cutFinset (P i)).card ≤ 2)
    (avoids : ∀ u (p : B.Walk u u), p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support) :
    ∃ f : ι ↪ (B.deleteEdges (⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))).ConnectedComponent,
      (∀ i, (f i).supp.toFinset = P i) ∧ (coreGraph B P f).IsAcyclic ∧
      (coreGraph B P f).edgeSet.ncard =
        (Finset.univ.filter (fun i => (B.cutFinset (P i)).card = 2)).card ∧
      ∀ u v, (coreGraph B P f).Reachable u v ↔ B.Reachable u.val.out v.val.out :=
  Internal.exists_core_forest B P connected disjoint separate boundary avoids

end Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression
