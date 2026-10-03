/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Marks on the small components attached to shaded paths

Monien and Preis assign two marks for each shaded thin path. If the path
has one red attachment, its small component gets both marks; if it has
two, each attachment contributes one mark. The weight `3 - α` on each
attachment implements these two cases once `1 ≤ α ≤ 2` is proved.

The finite map keeps multiplicities, including parallel red attachments
and marks from different paths on the same black component. Its `degree`
is the total number of marks. Values outside the thin-path hypotheses
are defined as well but need not have total two per path.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem

open scoped Classical

/-- Marks assigned to small black components by the selected shaded thin paths. -/
noncomputable def attachmentMarks {V E : Type} [Fintype V] [Fintype E]
    (B : SimpleGraph V) (R : Multigraph V E) (U : Finset V) (M : Nat)
    (shaded : Finset (thinComponents B R U M)) : B.ConnectedComponent →₀ ℕ :=
  ∑ i ∈ shaded, ∑ e ∈ attachmentEdges B R (region B U i.val) M,
    Finsupp.single (attachmentComponent B R (region B U i.val) M e)
      (3 - (attachmentEdges B R (region B U i.val) M).card)

/-- The count `k` and the small cyclic components fit together within the
original cycle rank. Cyclic components are counted once, regardless of their rank. -/
def SmallCycleBudget {V : Type} [Fintype V] (B : SimpleGraph V) (M k : Nat) : Prop :=
  ∀ cyclic : Finset B.ConnectedComponent,
    (∀ C ∈ cyclic, Fintype.card C ≤ M ∧ ¬ C.toSimpleGraph.IsAcyclic) →
    k + cyclic.card + Fintype.card V ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem
