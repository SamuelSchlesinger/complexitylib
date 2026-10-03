/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# Positive sets in a red/black graph

Monien and Preis's core lemma seeks a set with more internal red edges
than external black edges. The black graph is simple; the red graph retains
edge identities, allowing parallel edges created by suppressing boundary
vertices. Degree and density assumptions belong to the theorems that need
them, since the proof also deletes black edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack

open scoped Classical

/-- Red edges with both endpoints in the chosen set, counted with multiplicity. -/
noncomputable def internalEdges {V E : Type} [Fintype E] (R : Multigraph V E)
    (X : Finset V) : Finset E :=
  Finset.univ.filter fun e => R.fst e ∈ X ∧ R.snd e ∈ X

/-- More internal red edges than external black edges. -/
def Positive {V E : Type} [Fintype V] [Fintype E]
    (B : SimpleGraph V) (R : Multigraph V E) (X : Finset V) : Prop :=
  (B.cutFinset X).card < (internalEdges R X).card

end Algebraic.Cutwidth.Bisection.RedBlack
