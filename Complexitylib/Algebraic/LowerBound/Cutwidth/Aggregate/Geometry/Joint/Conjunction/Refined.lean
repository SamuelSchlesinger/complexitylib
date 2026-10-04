/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Joint.Conjunction.Family

/-!
# Separate information costs for two-variable and wider conjunctions

The support-graph bound pays for a family of two-variable conjunctions jointly.
Conjunctions with at least three variables retain the sharper one-eighth entropy
cost instead of being weakened to the graph's edge cost.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open Entropy
open scoped Classical

variable {V I J : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Two selected conjunction families retain their separate joint and marginal costs. -/
noncomputable def evalLiteralsFamiliesRefinedWeightBound
    (L₂ : I → Finset (V × Bool)) (L₃ : J → Finset (V × Bool))
    (two : ∀ i, 2 ≤ (literalVars (L₂ i)).card)
    (three : ∀ j, 3 ≤ (literalVars (L₃ j)).card) :
    WeightBound (fun x => ((fun i => evalLiterals (L₂ i) x),
      fun j => evalLiterals (L₃ j) x))
      (Fintype.card I * Graph.edgeCost + Fintype.card V * Graph.vertexCost +
        Fintype.card J * Real.binEntropy (1 / 8)) := by
  have narrow := evalLiteralsFamilyWeightBound L₂ two
  have wide : WeightBound (fun x j => evalLiterals (L₃ j) x)
      (Fintype.card J * Real.binEntropy (1 / 8)) := by
    simpa using WeightBound.pi fun j => evalLiteralsEighthWeightBoundOfThreeLe (three j)
  exact narrow.prod wide

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
