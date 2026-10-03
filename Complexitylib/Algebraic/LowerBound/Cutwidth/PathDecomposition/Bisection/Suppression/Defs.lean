/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs

/-!
# Suppressing an independent cut boundary

A boundary vertex with two interior neighbors becomes a red edge between
them. Its identity is the edge identity, so parallel edges are preserved.
The black graph is the original graph induced on the interior vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

/-- A loopless red graph on the interior of a side. Its edges are precisely
the boundary vertices, and red incidence is original boundary adjacency. -/
structure BoundarySuppression {W : Type} (H : SimpleGraph W) (S : Finset W) where
  /-- Suppressed boundary vertices retain distinct edge identities. -/
  red : Multigraph {v : W // v ∈ S \ cutBoundary H S} {c : W // c ∈ cutBoundary H S}
  /-- A boundary vertex has two distinct interior neighbors. -/
  loopless : red.Loopless
  /-- The two red endpoints are exactly the original interior neighbors. -/
  incident_iff : ∀ v c, red.Incident v c ↔ H.Adj c.val v.val

end Algebraic.Cutwidth.Bisection
