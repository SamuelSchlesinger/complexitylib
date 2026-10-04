/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Internal.Bound

/-!
# Joint entropy of signed two-variable conjunctions

For `m` signed conjunctions on `v` independent Boolean coordinates, the joint
message has a normalized weight of average natural-log cost at most
`m * (3/2 * log 2 - H(1/4)) + v * (H(1/4) - 3/4 * log 2)`.
Here `H` is binary entropy with natural logarithms. The weight certificate implies
the usual Shannon-entropy bound and applies directly to finite-fibre counting.
Parallel edges, arbitrary signs, and every finite primary-support graph are allowed.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- A joint weight for selected edges, charging only primary coordinates actually used. -/
noncomputable def weightBoundSelected (edge : E → SignedEdge V) (selected : Finset E) :
    WeightBound (tuple edge selected)
      (selected.card * edgeCost +
        (support (fun e => (edge e).left) (fun e => (edge e).right) selected).card *
          vertexCost) :=
  Internal.weightBoundSelected edge selected

/-- **The graph entropy bound.** Joint signed-conjunction messages cost at most
`m (3/2 log 2 - H(1/4)) + v (H(1/4) - 3/4 log 2)` on `v` independent uniform bits. -/
noncomputable def weightBound [Fintype E] (edge : E → SignedEdge V) :
    WeightBound (fun x e => (edge e).eval x)
      (Fintype.card E * edgeCost + Fintype.card V * vertexCost) :=
  Internal.weightBound edge

/-- If no edge-message fibre has more than `K` inputs, the joint cost bounds the input count. -/
theorem input_le_cost_of_fibres [Fintype E] (edge : E → SignedEdge V) {K : ℕ}
    (hK : 0 < K)
    (fibres : ∀ message, (Finset.univ.filter fun x =>
      (fun e => (edge e).eval x) = message).card ≤ K) :
    Fintype.card V * Real.log 2 ≤ Real.log K +
      Fintype.card E * edgeCost + Fintype.card V * vertexCost := by
  have bound := (weightBound edge).log_card_le hK (fun message => by
    convert fibres message using 1
    congr 1
    ext x
    simp only [Finset.mem_filter])
  simpa only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow, add_assoc] using bound

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
