/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.BridgeQuotient.Defs

/-!
# The graph on the core pieces

Identify the region vertices of the region-boundary quotient and suppress
them. The remaining vertices represent the connected pieces outside all
regions; a suppressed region supplies a connection between its neighboring
pieces. This is the core graph used by the weighted-tree argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression

open scoped Classical

/-- Suppress the designated region vertices of the boundary quotient. -/
noncomputable def coreGraph {V ι : Type} [Fintype V] [Fintype ι]
    (B : SimpleGraph V) (P : ι → Finset V)
    (f : ι ↪ (B.deleteEdges (⋃ i, (B.cutFinset (P i) : Set (Sym2 V)))).ConnectedComponent) :
    SimpleGraph {C // C ∉ Finset.univ.image f} :=
  graph (BridgeQuotient.ofRegions B P) (Finset.univ.image f)

end Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression
