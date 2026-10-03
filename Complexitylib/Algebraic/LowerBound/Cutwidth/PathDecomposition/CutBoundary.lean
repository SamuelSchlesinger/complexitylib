/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Internal

/-!
# Boundary counts for the bisection assembly

Both vertex boundaries are bounded by the number of crossing edges. Cutting
an induced subgraph on the same side cannot increase that edge count.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- The two orientations of a cut have the same crossing edges. -/
theorem cutFinset_compl (S : Finset W) : H.cutFinset Sᶜ = H.cutFinset S :=
  PathDecomposition.Internal.cutFinset_compl H S

/-- Each boundary vertex can be charged to a distinct crossing edge. -/
theorem card_cutBoundary_le (S : Finset W) :
    (cutBoundary H S).card ≤ (H.cutFinset S).card :=
  PathDecomposition.Internal.card_cutBoundary_le H S

/-- Inducing a graph cannot increase the number of edges crossing a fixed side. -/
theorem card_cutFinset_induce_le (S : Finset W) (T : Set W)
    [DecidablePred (· ∈ T)] [Fintype T] :
    ((H.induce T).cutFinset (S.subtype (· ∈ T))).card ≤ (H.cutFinset S).card :=
  PathDecomposition.Internal.card_cutFinset_induce_le H S T

end Algebraic.Cutwidth
