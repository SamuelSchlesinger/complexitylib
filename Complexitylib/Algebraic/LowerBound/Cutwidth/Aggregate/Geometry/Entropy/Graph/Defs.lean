/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Graph.Support

/-!
# The joint weight bound for signed two-variable conjunctions

An edge contributes its two-literal conjunction to the message. The entropy bound
charges each edge and each used primary coordinate, allowing arbitrary parallel
edges and signs and making no graph acyclicity assumption.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph

/-- The natural-log cost charged to each edge in the joint message. -/
noncomputable def edgeCost : ℝ := 3 / 2 * Real.log 2 - Real.binEntropy (1 / 4)

/-- The natural-log cost charged to each primary variable used by the message. -/
noncomputable def vertexCost : ℝ := Real.binEntropy (1 / 4) - 3 / 4 * Real.log 2

/-- The message consisting of the conjunction values of selected edges. -/
def tuple {V E : Type*} (edge : E → SignedEdge V) (selected : Finset E)
    (x : V → Bool) : selected → Bool := fun e => (edge e).eval x

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy.Graph
