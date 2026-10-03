/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Boundary.Internal

/-!
# Joining the two boundaries of a graph cut

The boundary transition in Fomin and Høie's *Pathwidth of cubic graphs and
exact algorithms* (2006), Theorem 5, has width at most the number of crossing
edges. This finite lemma does not require a degree bound. It is one part of
the pathwidth proof, completed in `Bisection` from the still unproved
sharp cubic bisection theorem.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

/-- If every vertex has a neighbor across a cut, there is a path decomposition
starting with one side and ending with the other, of width at most the cut size.
Edges within either side are covered by its endpoint bag. -/
theorem exists_between_of_crossing {W : Type} [Fintype W] (H : SimpleGraph W)
    (S : Finset W)
    (left : ∀ u ∈ S, ∃ v ∉ S, H.Adj u v)
    (right : ∀ v ∉ S, ∃ u ∈ S, H.Adj u v) :
    ∃ (D : PathDecomposition H) (first last : Fin D.length),
      (∀ i, first ≤ i ∧ i ≤ last) ∧ D.bag first = S ∧ D.bag last = Sᶜ ∧
        ∀ i, (D.bag i).card ≤ (H.cutFinset S).card + 1 :=
  Internal.exists_boundaryTransition H S left right

end Algebraic.Cutwidth.PathDecomposition
