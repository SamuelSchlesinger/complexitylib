/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# The graph of components separated by designated edges

Delete a set of designated edges and take the connected components of what
remains. Two components are adjacent in the quotient when an original edge
joins them. When the designated edges are bridges, this quotient is a
forest, even if the contracted components themselves contain cycles.
This is the contraction used in Monien and Preis's red/black tree argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient

/-- Contract the components remaining after deleting `F`, retaining the original
adjacencies between distinct components. -/
def graph {V : Type} (B : SimpleGraph V) (F : Set (Sym2 V)) :
    SimpleGraph (B.deleteEdges F).ConnectedComponent where
  Adj C D := C ≠ D ∧ ∃ u ∈ C.supp, ∃ v ∈ D.supp, B.Adj u v
  symm := ⟨by
    rintro C D ⟨different, u, hu, v, hv, adjacent⟩
    exact ⟨different.symm, v, hv, u, hu, adjacent.symm⟩⟩
  loopless := ⟨fun _ ⟨different, _⟩ => different rfl⟩

/-- Contract the components remaining after deleting all boundaries of the given regions. -/
noncomputable def ofRegions {V ι : Type} [Fintype V] (B : SimpleGraph V) (P : ι → Finset V) :
    SimpleGraph (B.deleteEdges (⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))).ConnectedComponent :=
  graph B (⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))

end Algebraic.Cutwidth.Bisection.RedBlack.BridgeQuotient
