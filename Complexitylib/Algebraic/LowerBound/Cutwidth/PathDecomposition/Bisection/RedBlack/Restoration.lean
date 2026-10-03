/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Defs
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Internal

/-!
# Restoring the black cut of an added set

Monien and Preis's red/black argument temporarily disconnects thin paths.
Adding a path and its attached small components compensates for restoring
the deleted edges. This module proves the cut and red-edge accounting for
one such restoration. `Restoration.Family` proves a uniform size bound for
restoring an entire family of isolated regions with closed red attachments.

The added set may overlap the existing witness in whole black components.
The empty-cut condition on the overlap makes this precise; only red edges
not already internal to the witness count toward the compensation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] (B : SimpleGraph V) (R : Multigraph V E)

/-- After isolating `A`, a positive set `X` lifts back to `X ∪ A` if the
new internal red edges pay for the black boundary of `A` that still crosses.
An overlap is permitted when its black cut is empty. -/
theorem positive_restore_cut {X A : Finset V}
    (positive : Positive (B.deleteEdges (B.cutFinset A : Set (Sym2 V))) R X)
    (closed : B.cutFinset (X ∩ A) = ∅)
    (budget : (B.cutFinset A \ B.cutFinset X).card ≤
      (internalEdges R A \ internalEdges R X).card) : Positive B R (X ∪ A) :=
  Internal.positive_restore_cut B R positive closed budget

/-- An added set with at most two external black edges needs only one new
internal red edge when at least one of its black boundary edges meets the
old witness. This is the local compensation used for a disconnected thin path. -/
theorem positive_restore_two_boundary {X A : Finset V}
    (positive : Positive (B.deleteEdges (B.cutFinset A : Set (Sym2 V))) R X)
    (closed : B.cutFinset (X ∩ A) = ∅)
    (two : (B.cutFinset A).card ≤ 2)
    (crossing : (B.cutFinset A ∩ B.cutFinset X).Nonempty)
    (newRed : (internalEdges R A \ internalEdges R X).Nonempty) :
    Positive B R (X ∪ A) :=
  Internal.positive_restore_two_boundary B R positive closed two crossing newRed

end Algebraic.Cutwidth.Bisection.RedBlack
