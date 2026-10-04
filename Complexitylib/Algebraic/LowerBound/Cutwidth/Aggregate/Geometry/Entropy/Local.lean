/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Coordinates
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Cases

/-!
# Conditional weights for incident signed conjunctions

The finite two-, three-, and four-variable cases cover every overlap pattern of
an edge with one or two earlier incident edges. Coordinate embeddings transport
their certificates to arbitrary Boolean cubes. These local bounds make no
independence assumption about the remaining circuit messages.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A two-literal conjunction costs at most the entropy of a quarter-biased bit. -/
noncomputable def SignedEdge.weightBound (e : SignedEdge V) :
    WeightBound e.eval (Real.binEntropy (1 / 4)) := by
  unfold SignedEdge.eval
  simpa [SignedEdge.eval, pairBit, pairCoordinates, Function.comp_def] using
    (pairSeed e.leftSign e.rightSign).precompCoordinates
      (pairCoordinates e.left e.right e.distinct)

/-- A parent on the same two coordinates gives the chord cost, for every choice of signs. -/
noncomputable def SignedEdge.conditionalParallel (e f : SignedEdge V)
    (left : e.left = f.left) (right : e.right = f.right) :
    ConditionalWeightBound e.eval f.eval
      (3 / 2 * Real.log 2 - Real.binEntropy (1 / 4)) := by
  unfold SignedEdge.eval
  simpa [SignedEdge.eval, pairBit, pairCoordinates, Function.comp_def, ← left, ← right] using
    (pairParallel e.leftSign e.rightSign f.leftSign f.rightSign).precompCoordinates
      (pairCoordinates e.left e.right e.distinct)

/-- Edges sharing their left endpoint admit a three-quarter-bit conditional certificate. -/
noncomputable def SignedEdge.conditionalSharedLeft (e f : SignedEdge V)
    (left : e.left = f.left) :
    ConditionalWeightBound e.eval f.eval (3 / 4 * Real.log 2) := by
  by_cases right : e.right = f.right
  · exact (e.conditionalParallel f left right).mono parallel_le_extension
  · have distinct : e.left ≠ f.right := by simpa only [left] using f.distinct
    unfold SignedEdge.eval
    simpa [SignedEdge.eval, pairBit, tripleCoordinates, Function.comp_def, ← left] using
      (pairExtension e.leftSign e.rightSign f.leftSign f.rightSign).precompCoordinates
        (tripleCoordinates e.left e.right f.right e.distinct distinct right)

/-- Any earlier incident edge lowers the conditional cost to at most three quarters of a bit. -/
noncomputable def SignedEdge.conditionalOne (e f : SignedEdge V)
    (overlap : e.left = f.left ∨ e.left = f.right ∨
      e.right = f.left ∨ e.right = f.right) :
    ConditionalWeightBound e.eval f.eval (3 / 4 * Real.log 2) := by
  by_cases h₁ : e.left = f.left
  · exact e.conditionalSharedLeft f h₁
  by_cases h₂ : e.left = f.right
  · simpa only [SignedEdge.eval_reverse] using e.conditionalSharedLeft f.reverse h₂
  by_cases h₃ : e.right = f.left
  · simpa only [SignedEdge.eval_reverse] using e.reverse.conditionalSharedLeft f h₃
  have h₄ := ((overlap.resolve_left h₁).resolve_left h₂).resolve_left h₃
  simpa only [SignedEdge.eval_reverse] using e.reverse.conditionalSharedLeft f.reverse h₄

/-- Parents oriented toward the target endpoints supply the remaining-edge certificate. -/
noncomputable def SignedEdge.conditionalTwoLeft (e f g : SignedEdge V)
    (left : e.left = f.left) (right : e.right = g.left) :
    ConditionalWeightBound e.eval (fun x => (f.eval x, g.eval x))
      (3 / 2 * Real.log 2 - Real.binEntropy (1 / 4)) := by
  by_cases parallelF : e.right = f.right
  · exact (e.conditionalParallel f left parallelF).withRightParent g.eval
  by_cases parallelG : e.left = g.right
  · have bound := (e.conditionalParallel g.reverse parallelG right).withLeftParent f.eval
    simpa only [SignedEdge.eval_reverse] using bound
  have ef : e.left ≠ f.right := by simpa only [left] using f.distinct
  have eg : e.right ≠ g.right := by simpa only [right] using g.distinct
  by_cases shared : f.right = g.right
  · unfold SignedEdge.eval
    simpa [pairBit, tripleCoordinates, Function.comp_def,
      ← left, ← right, ← shared] using
      (pairTriangle e.leftSign e.rightSign f.leftSign f.rightSign
        g.leftSign g.rightSign).precompCoordinates
          (tripleCoordinates e.left e.right f.right e.distinct ef parallelF)
  · unfold SignedEdge.eval
    simpa [pairBit, quadCoordinates, Function.comp_def,
      ← left, ← right] using
      (pairDisjoint e.leftSign e.rightSign f.leftSign f.rightSign
        g.leftSign g.rightSign).precompCoordinates
          (quadCoordinates e.left e.right f.right g.right e.distinct ef parallelG
            parallelF eg shared)

/-- Earlier incident edges at both endpoints give the chord cost, including parallel edges. -/
noncomputable def SignedEdge.conditionalTwo (e f g : SignedEdge V)
    (left : e.left = f.left ∨ e.left = f.right)
    (right : e.right = g.left ∨ e.right = g.right) :
    ConditionalWeightBound e.eval (fun x => (f.eval x, g.eval x))
      (3 / 2 * Real.log 2 - Real.binEntropy (1 / 4)) := by
  by_cases hl : e.left = f.left <;> by_cases hr : e.right = g.left
  · exact e.conditionalTwoLeft f g hl hr
  · simpa only [SignedEdge.eval_reverse] using
      e.conditionalTwoLeft f g.reverse hl (right.resolve_left hr)
  · simpa only [SignedEdge.eval_reverse] using
      e.conditionalTwoLeft f.reverse g (left.resolve_left hl) hr
  · simpa only [SignedEdge.eval_reverse] using
      e.conditionalTwoLeft f.reverse g.reverse (left.resolve_left hl) (right.resolve_left hr)

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
