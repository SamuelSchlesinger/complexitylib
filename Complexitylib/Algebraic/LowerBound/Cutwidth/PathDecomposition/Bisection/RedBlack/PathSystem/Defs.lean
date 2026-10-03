/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph

/-!
# Canonical connected regions among eligible vertices

The path system in Monien and Preis's red/black argument starts with an
eligible set of unmarked black degree-two vertices. Its regions are the
connected components induced on that set, viewed back in the original
vertex type. The definition also makes sense for any eligible set; degree
assumptions enter the theorems about spanning paths and boundary size.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem

open scoped Classical

/-- The vertices of an induced connected component, in the ambient vertex type. -/
noncomputable def region {V : Type} (B : SimpleGraph V) (U : Finset V)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent) : Finset V :=
  C.supp.toFinset.image Subtype.val

/-- Red edges joining the region to a black component of at most `M` vertices. -/
noncomputable def attachmentEdges {V E : Type} [Fintype V] [Fintype E]
    (B : SimpleGraph V) (R : Multigraph V E) (P : Finset V) (M : Nat) : Finset E :=
  Finset.univ.filter fun e =>
    (R.fst e ∈ P ∧ Fintype.card (B.connectedComponentMk (R.snd e)) ≤ M) ∨
      (R.snd e ∈ P ∧ Fintype.card (B.connectedComponentMk (R.fst e)) ≤ M)

/-- The attached black component, choosing the second endpoint when it qualifies.
Only values on `attachmentEdges` are used. -/
noncomputable def attachmentComponent {V E : Type} [Fintype V]
    (B : SimpleGraph V) (R : Multigraph V E) (P : Finset V) (M : Nat) (e : E) :
    B.ConnectedComponent :=
  if R.fst e ∈ P ∧ Fintype.card (B.connectedComponentMk (R.snd e)) ≤ M then
    B.connectedComponentMk (R.snd e)
  else B.connectedComponentMk (R.fst e)

/-- The vertices of the attached small black component. -/
noncomputable def attachment {V E : Type} [Fintype V]
    (B : SimpleGraph V) (R : Multigraph V E) (P : Finset V) (M : Nat) (e : E) : Finset V :=
  (attachmentComponent B R P M e).supp.toFinset

/-- Eligible components with at least one red attachment per `M` vertices. -/
noncomputable def thinComponents {V E : Type} [Fintype V] [Fintype E]
    (B : SimpleGraph V) (R : Multigraph V E) (U : Finset V) (M : Nat) :
    Finset (B.induce {v | v ∈ U}).ConnectedComponent :=
  let : Fintype (B.induce {v | v ∈ U}).ConnectedComponent := Fintype.ofFinite _
  Finset.univ.filter fun C =>
    (region B U C).card ≤ M * (attachmentEdges B R (region B U C) M).card

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem
