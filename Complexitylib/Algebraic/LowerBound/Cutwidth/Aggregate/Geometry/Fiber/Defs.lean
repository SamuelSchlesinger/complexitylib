/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Defs

/-!
# Majority inputs of signed conjunction summaries

For a two-variable signed conjunction, `false` is its three-to-one majority
output. A family has disjoint primary pairs when its endpoint map is injective.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open Entropy

/-- The two primary endpoints of every selected signed conjunction. -/
def endpoint {E V : Type*} (edge : E → SignedEdge V) (p : E × Bool) : V :=
  if p.2 then (edge p.1).right else (edge p.1).left

/-- Inputs on which every selected conjunction takes its majority output. -/
noncomputable def majorityInputs {E V : Type*} [Fintype E] [Fintype V]
    (edge : E → SignedEdge V) : Finset (V → Bool) := by
  classical
  exact Finset.univ.filter fun x => ∀ e, (edge e).eval x = false

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
