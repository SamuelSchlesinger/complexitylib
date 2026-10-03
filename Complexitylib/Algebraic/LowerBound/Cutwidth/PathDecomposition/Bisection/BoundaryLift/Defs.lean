/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary.Defs

/-!
# Lifting a red/black witness through the cut boundary

In the normalized side of Monien and Preis's helpful-set argument, each
boundary vertex has one outside neighbor and two nonboundary neighbors.
It represents a red edge between those two neighbors. Boundary vertices
remain distinct, so parallel red edges retain their multiplicity.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

/-- Add every boundary vertex adjacent to the chosen interior set. -/
noncomputable def boundaryLift {W : Type} (H : SimpleGraph W) (S X : Finset W) : Finset W :=
  X ∪ (cutBoundary H S).filter (fun c => ∃ x ∈ X, H.Adj c x)

/-- Boundary vertices incident to at least two chosen vertices. When each
boundary vertex has two interior neighbors, these count internal red edges,
including parallel edges represented by different boundary vertices. -/
noncomputable def sharedBoundary {W : Type} [Fintype W] (H : SimpleGraph W)
    (S X : Finset W) : Finset W :=
  (cutBoundary H S).filter (fun c => 2 ≤ (H.neighborFinset c ∩ X).card)

end Algebraic.Cutwidth.Bisection
