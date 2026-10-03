/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Components.Internal

/-!
# Path decompositions of disconnected graphs

Concatenating the decompositions of the connected components preserves
their common bag-size bound. No vertex belongs to two component blocks.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

/-- Combine component decompositions without increasing any bag's size.
The result also covers the empty graph, for which zero bags suffice. -/
theorem exists_of_components {W : Type} [Fintype W] {H : SimpleGraph W} {b : Nat}
    (parts : ∀ C : H.ConnectedComponent,
      ∃ D : PathDecomposition C.toSimpleGraph, ∀ i, (D.bag i).card ≤ b) :
    ∃ D : PathDecomposition H, ∀ i, (D.bag i).card ≤ b :=
  Internal.exists_of_components parts

end Algebraic.Cutwidth.PathDecomposition
