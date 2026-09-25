/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferIteration
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferedPhaseCost

/-!
# A near-linear bound for the complete nonuniform scheduler

The exact recursive cost sum is bounded by `total * 2^width` times an
explicit fixed polynomial in the address width, request width, field width,
and ceiling logarithm of the original request count.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferIteration

open Sorting BufferInput BufferModel
open scoped LinearAlgebra.Projectivization

/-- Polynomial overhead per original request and field scalar. -/
def polynomialFactor (total dimension width requestWidth : Nat) : Nat :=
  10000 * (FiniteParameters.binaryDepth total + 1) * (14 + 18 * (dimension * width)) *
    BufferedPhase.height total dimension width requestWidth ^ 5

/-- Sum at most one uniform phase bound for every halving depth. -/
theorem costBound_le_phaseCount (counts : completed + networkRecords requestDepth = total) :
    costBound total dimension width requestWidth requestDepth completed ≤
      (requestDepth + 1) * (10000 * (total * 2 ^ width * (14 + 18 * (dimension * width))) *
        BufferedPhase.height total dimension width requestWidth ^ 5) := by
  induction requestDepth generalizing completed with
  | zero =>
      simpa only [costBound, Nat.zero_add, Nat.one_mul] using
        (BufferedPhase.costBound_le (requestDepth := 0) (by omega : completed ≤ total) (by omega))
  | succ depth inductionHypothesis =>
      have nextCounts : (completed + networkRecords depth) + networkRecords depth = total := by
        simpa only [networkRecords, Nat.add_assoc] using counts
      have nextBound := inductionHypothesis nextCounts
      have phaseBound := BufferedPhase.costBound_le (requestDepth := depth + 1)
        (dimension := dimension) (width := width) (requestWidth := requestWidth)
        (by omega : completed ≤ total) (by omega)
      rw [costBound]
      exact (Nat.add_le_add phaseBound nextBound).trans_eq (by ring)

/-- The complete phase sum is linear in the original point budget. -/
theorem costBound_le_linear (counts : completed + networkRecords requestDepth = total) :
    costBound total dimension width requestWidth requestDepth completed ≤
      total * 2 ^ width * polynomialFactor total dimension width requestWidth := by
  have requestBound := BufferedPhase.requestDepth_le (by omega : networkRecords requestDepth ≤ total)
  calc
    _ ≤ _ := costBound_le_phaseCount counts
    _ ≤ (FiniteParameters.binaryDepth total + 1) *
        (10000 * (total * 2 ^ width * (14 + 18 * (dimension * width))) *
          BufferedPhase.height total dimension width requestWidth ^ 5) := by gcongr
    _ = _ := by unfold polynomialFactor; ring

/-- One fixed, near-linear-size circuit completes every valid input buffer
under the projective-direction budget. -/
theorem existsCircuit_linear
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (counts : completed + networkRecords requestDepth = total)
    (budget : 512 * total * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (targetProjection : Fin (dimension * width) → Fin requestWidth) :
    ∃ scheduler : Circuit DeMorgan.signature
      (inputWidth completed (networkRecords requestDepth) requestWidth (2 ^ width) (dimension * width))
      (inputWidth total 0 requestWidth (2 ^ width) (dimension * width)),
      scheduler.cost DeMorgan.standardCost ≤ total * 2 ^ width * polynomialFactor total dimension width requestWidth ∧
      Transforms positive targetProjection scheduler total := by
  obtain ⟨scheduler, bound, correct⟩ := existsCircuit_complete positive dimensionPositive counts budget targetProjection
  exact ⟨scheduler, bound.trans (costBound_le_linear counts), correct⟩

end Algebraic.MassProduction.Nonuniform.BufferIteration
