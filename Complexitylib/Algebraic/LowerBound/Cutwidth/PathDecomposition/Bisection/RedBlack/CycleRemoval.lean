/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal.Core

/-!
# Breaking all cycles through designated edges

A finite graph admits deletion of designated edges so that every retained
designated edge is a bridge, while reachability and connected components
are preserved. The number deleted is at most the original cycle rank:
`|E| - |V| + number of components`, expressed without natural subtraction.
Untouched cyclic components reserve one unit of this rank each, in addition
to the units used by deleted edges.

A cycle meeting a connected region of black degree at most two contains
every boundary edge of that region. Designating one boundary edge per
region therefore suffices to break all cycles through the regions. If
the designated edges are distinct, at most the original cycle rank many
regions need be isolated, and the result has no cycle through any region.
Deleting full cuts also preserves reachability between vertices outside
the selected regions: after the first edge deletion, a simple path cannot
enter and leave a region through its sole remaining boundary edge.

This supplies cycle selection for a given thin-path system in Monien and
Preis's proof. `PathSystem` constructs and instantiates that system.
`BridgeQuotient` contracts the pieces between surviving boundaries to a
forest. `PathSystem.Marks` counts the initial attachment marks and reserves
rank for small cyclic components. Preserving these invariants through the
weighted-tree reorganization remains a separate obligation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

/-- Every cyclic component uses at least one unit of cycle rank. -/
theorem card_vertices_add_cyclic_le (cyclic : Finset B.ConnectedComponent)
    (cycles : ∀ C ∈ cyclic, ¬ C.toSimpleGraph.IsAcyclic) :
    Fintype.card V + cyclic.card ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent :=
  CycleRemoval.Internal.card_vertices_add_cyclic_le B cyclic cycles

/-- Reachability-preserving deletions and untouched cyclic components together
use at most the original cycle rank. -/
theorem card_removed_add_untouched_cyclic_le (removed : Finset (Sym2 V))
    (edges : removed ⊆ B.edgeFinset)
    (reachable : (B.deleteEdges (removed : Set (Sym2 V))).Reachable = B.Reachable)
    (cyclic : Finset B.ConnectedComponent)
    (cycles : ∀ C ∈ cyclic, ¬ C.toSimpleGraph.IsAcyclic)
    (kept : ∀ C ∈ cyclic, ∀ {u v}, u ∈ C.supp → v ∈ C.supp →
      B.Adj u v → s(u, v) ∉ removed) :
    removed.card + cyclic.card + Fintype.card V ≤
      B.edgeFinset.card + Nat.card B.ConnectedComponent :=
  CycleRemoval.Internal.card_removed_add_untouched_cyclic_le B removed edges reachable
    cyclic cycles kept

/-- Remove designated edges from cycles without changing any reachability
relation. Every designated edge that survives is a bridge, and the number
removed is bounded by the original cycle rank. -/
theorem exists_delete_to_bridges
    (eligible : Finset (Sym2 V)) (edges : eligible ⊆ B.edgeFinset) :
    ∃ removed ⊆ eligible,
      (B.deleteEdges (removed : Set (Sym2 V))).Reachable = B.Reachable ∧
      (∀ e ∈ eligible \ removed, (B.deleteEdges (removed : Set (Sym2 V))).IsBridge e) ∧
      removed.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent :=
  CycleRemoval.Internal.exists_delete_to_bridges B eligible edges

/-- A cycle that meets a connected region of degree at most two traverses
every boundary edge of that region. -/
theorem cycle_contains_boundary_of_meets_region {P : Finset V}
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) {u : V} {p : B.Walk u u}
    (cycle : p.IsCycle) (meets : ∃ v ∈ P, v ∈ p.support)
    {e : Sym2 V} (boundary : e ∈ B.cutFinset P) : e ∈ p.edges :=
  CycleRemoval.Internal.cycle_contains_boundary_of_meets_region B connected degree
    cycle meets boundary

/-- Select regions to isolate so that no cycle meets any original region.
At most the original cycle rank many regions are selected. Deleting only
their chosen boundary edges preserves reachability; deleting their whole
cuts additionally isolates them. -/
theorem exists_isolate_regions_without_cycles {ι : Type} [Fintype ι] (P : ι → Finset V)
    (connected : ∀ i, (B.induce {v | v ∈ P i}).Connected)
    (degree : ∀ i, ∀ v ∈ P i, B.degree v ≤ 2)
    (chosen : ι → Sym2 V) (injective : Function.Injective chosen)
    (boundary : ∀ i, chosen i ∈ B.cutFinset (P i)) :
    ∃ indices : Finset ι,
      indices.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent ∧
      (B.deleteEdges (indices.image chosen : Set (Sym2 V))).Reachable = B.Reachable ∧
      ∀ u (p : (B.deleteEdges
          (indices.biUnion (fun i => B.cutFinset (P i)) : Set (Sym2 V))).Walk u u),
        p.IsCycle → ∀ i v, v ∈ P i → v ∉ p.support :=
  CycleRemoval.Internal.exists_isolate_regions_without_cycles B P connected degree
    chosen injective boundary

/-- Isolating regions with at most two boundary edges preserves reachability
between vertices outside all selected regions, provided deleting their chosen
single boundary edges preserves reachability. No disjointness is needed. -/
theorem reachable_after_isolating {ι : Type} (P : ι → Finset V)
    (chosen : ι → Sym2 V) (indices : Finset ι)
    (two : ∀ i ∈ indices, (B.cutFinset (P i)).card ≤ 2)
    (boundary : ∀ i ∈ indices, chosen i ∈ B.cutFinset (P i))
    (preserved : (B.deleteEdges (indices.image chosen : Set (Sym2 V))).Reachable = B.Reachable)
    {u v : V} (hu : ∀ i ∈ indices, u ∉ P i) (hv : ∀ i ∈ indices, v ∉ P i) :
    (B.deleteEdges (indices.biUnion (fun i => B.cutFinset (P i)) : Set (Sym2 V))).Reachable u v ↔
      B.Reachable u v :=
  CycleRemoval.Internal.reachable_after_isolating B P chosen indices two boundary preserved hu hv

end Algebraic.Cutwidth.Bisection.RedBlack
