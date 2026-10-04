/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Assembly
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local

/-!
# Actual signed-edge weight bounds

The local signed-conjunction certificates discharge the three cases of the
edge-insertion induction. Enlarging the used support to the ambient vertex set
then gives a bound stated only in terms of the numbers of edges and variables.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal

open scoped Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The actual local certificates give a weight for any selected edge message. -/
noncomputable def weightBoundSelected (edge : E → SignedEdge V) (selected : Finset E) :
    WeightBound (tuple edge selected)
      (selected.card * edgeCost +
        (support (fun e => (edge e).left) (fun e => (edge e).right) selected).card *
          vertexCost) :=
  Classical.choice (exists_weightBound_tuple_of_local SignedEdge.weightBound
    SignedEdge.conditionalOne SignedEdge.conditionalTwo edge selected)

/-- The tuple on all indices is equivalent to the ordinary function space. -/
noncomputable def tupleUnivEquiv [Fintype E] : (↥(Finset.univ : Finset E) → Bool) ≃
    (E → Bool) where
  toFun m e := m ⟨e, Finset.mem_univ e⟩
  invFun m e := m e
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full edge message has the asserted cost in the ambient number of variables. -/
noncomputable def weightBound [Fintype E] (edge : E → SignedEdge V) :
    WeightBound (fun x e => (edge e).eval x)
      (Fintype.card E * edgeCost + Fintype.card V * vertexCost) := by
  have bound := (weightBoundSelected edge Finset.univ).equiv (tupleUnivEquiv (E := E))
  have used : ((support (fun e => (edge e).left) (fun e => (edge e).right)
      (Finset.univ : Finset E)).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Finset.card_le_univ
      (support (fun e => (edge e).left) (fun e => (edge e).right) Finset.univ))
  apply bound.mono
  simp only [Finset.card_univ]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right used vertexCost_nonneg)

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal
