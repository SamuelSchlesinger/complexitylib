/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferedPhase

/-!
# The complete fixed halving iteration

Compose one universal compacted phase for each pending power of two, ending
with the singleton phase. The circuit completes every original request and
preserves the disjoint-schedule invariant. Its cost is bounded by the exact
recursive sum of the explicit phase bounds.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferIteration

open Sorting BufferInput BufferModel
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- Existence package with visible buffer-size arguments, so equalities of
record counts transport the circuit and its semantic contract together. -/
private def RealizesBound (positive : 0 < width)
    (targetProjection : Fin (dimension * width) → Fin requestWidth)
    (total completed pending nextCompleted nextPending bound : Nat) : Prop :=
  ∃ gates, ∃ scheduler : Circuit DeMorgan.signature
    (inputWidth completed pending requestWidth (2 ^ width) (dimension * width)) gates
    (inputWidth nextCompleted nextPending requestWidth (2 ^ width) (dimension * width)),
    scheduler.cost DeMorgan.standardCost ≤ bound ∧
      Transforms positive targetProjection scheduler total

/-- Sum of the explicit phase bounds along the fixed halving schedule. -/
def costBound (total dimension width requestWidth : Nat) : Nat → Nat → Nat
  | 0, completed => BufferedPhase.costBound total completed 0 dimension width requestWidth
  | depth + 1, completed =>
      BufferedPhase.costBound total completed (depth + 1) dimension width requestWidth +
        costBound total dimension width requestWidth depth (completed + networkRecords depth)

/-- One concrete circuit completes all halving phases and leaves no pending
requests, preserving the full encoded request and geometric invariants. -/
theorem existsCircuit
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (counts : completed + networkRecords requestDepth = total)
    (budget : 512 * total * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (targetProjection : Fin (dimension * width) → Fin requestWidth) :
    ∃ gates, ∃ scheduler : Circuit DeMorgan.signature
      (inputWidth completed (networkRecords requestDepth) requestWidth (2 ^ width) (dimension * width)) gates
      (inputWidth (completed + networkRecords requestDepth) 0 requestWidth (2 ^ width) (dimension * width)),
      scheduler.cost DeMorgan.standardCost ≤ costBound total dimension width requestWidth requestDepth completed ∧
      Transforms positive targetProjection scheduler total := by
  change RealizesBound positive targetProjection total completed (networkRecords requestDepth)
    (completed + networkRecords requestDepth) 0 (costBound total dimension width requestWidth requestDepth completed)
  induction requestDepth generalizing completed with
  | zero =>
      exact BufferedPhase.existsCircuit positive dimensionPositive counts budget targetProjection
  | succ depth inductionHypothesis =>
      have stepExists := BufferedPhase.existsCircuit (requestDepth := depth + 1)
        positive dimensionPositive counts budget targetProjection
      change RealizesBound positive targetProjection total completed (networkRecords (depth + 1))
        (completed + acceptedCount (depth + 1)) (pendingCount (depth + 1))
        (BufferedPhase.costBound total completed (depth + 1) dimension width requestWidth) at stepExists
      rw [acceptedCount_succ, pendingCount_succ] at stepExists
      obtain ⟨stepGates, step, stepBound, stepCorrect⟩ := stepExists
      have nextCounts : (completed + networkRecords depth) + networkRecords depth = total := by
        simpa only [networkRecords, Nat.add_assoc] using counts
      obtain ⟨tailGates, tail, tailBound, tailCorrect⟩ := inductionHypothesis nextCounts
      have composed : ∃ gates, ∃ scheduler : Circuit DeMorgan.signature
          (inputWidth completed (networkRecords (depth + 1)) requestWidth (2 ^ width) (dimension * width)) gates
          (inputWidth ((completed + networkRecords depth) + networkRecords depth) 0
            requestWidth (2 ^ width) (dimension * width)),
          scheduler.cost DeMorgan.standardCost ≤
            BufferedPhase.costBound total completed (depth + 1) dimension width requestWidth +
              costBound total dimension width requestWidth depth (completed + networkRecords depth) ∧
          Transforms positive targetProjection scheduler total := by
        refine ⟨_, tail.comp step, ?_, ?_⟩
        · rw [Circuit.cost_comp]
          exact Nat.add_le_add stepBound tailBound
        · exact Transforms.comp positive targetProjection step tail stepCorrect tailCorrect
      change RealizesBound positive targetProjection total completed (networkRecords (depth + 1))
        ((completed + networkRecords depth) + networkRecords depth) 0
        (BufferedPhase.costBound total completed (depth + 1) dimension width requestWidth +
          costBound total dimension width requestWidth depth (completed + networkRecords depth)) at composed
      simpa only [costBound, networkRecords, Nat.add_assoc] using composed

/-- The completed-count equality may be used to expose an output buffer
indexed by the original total request count. -/
theorem existsCircuit_complete
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (counts : completed + networkRecords requestDepth = total)
    (budget : 512 * total * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (targetProjection : Fin (dimension * width) → Fin requestWidth) :
    ∃ gates, ∃ scheduler : Circuit DeMorgan.signature
      (inputWidth completed (networkRecords requestDepth) requestWidth (2 ^ width) (dimension * width)) gates
      (inputWidth total 0 requestWidth (2 ^ width) (dimension * width)),
      scheduler.cost DeMorgan.standardCost ≤ costBound total dimension width requestWidth requestDepth completed ∧
      Transforms positive targetProjection scheduler total := by
  have result := existsCircuit positive dimensionPositive counts budget targetProjection
  change RealizesBound positive targetProjection total completed (networkRecords requestDepth)
    (completed + networkRecords requestDepth) 0 (costBound total dimension width requestWidth requestDepth completed) at result
  rw [counts] at result
  exact result

end Algebraic.MassProduction.Nonuniform.BufferIteration
