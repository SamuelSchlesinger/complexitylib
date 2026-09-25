/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferStepCorrectness
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferTransform
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferPhaseState
public import Complexitylib.Algebraic.MassProduction.Nonuniform.UniversalGeometricPhase

/-!
# A universal compacted halving step

For fixed buffer sizes and field parameters, one concrete circuit accepts
half the pending requests and produces the next encoded buffer. The circuit
works for every original request dataset with distinct identities and the
stated target projection. All menu choices precede the input and state.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferedPhase

open Sorting BufferInput BufferModel
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- Sorting depth of the fixed universal menu for this pending count. -/
def menuDepth (total requestDepth dimension width : Nat) : Nat :=
  phaseMenuDepth total (networkRecords requestDepth) (dimension * width)

/-- Source records plus all generated candidate points. -/
def routingRecords (total completed requestDepth dimension width : Nat) : Nat :=
  completed * 2 ^ width + networkRecords (menuDepth total requestDepth dimension width + requestDepth + width)

/-- Canonical routing depth for shared occupancy lookup. -/
def routingDepth (total completed requestDepth dimension width : Nat) : Nat :=
  FiniteParameters.binaryDepth (routingRecords total completed requestDepth dimension width)

/-- Canonical padding gives the exact required occupancy-router capacity. -/
theorem recordCount (total completed requestDepth dimension width : Nat) :
    completed * 2 ^ width + networkRecords (menuDepth total requestDepth dimension width + requestDepth + width) +
      FiniteParameters.paddingCount (routingRecords total completed requestDepth dimension width) =
        networkRecords (routingDepth total completed requestDepth dimension width) :=
  FiniteParameters.records_add_paddingCount _

/-- The explicit cost bound for one complete compacted buffer step. -/
def costBound (total completed requestDepth dimension width requestWidth : Nat) : Nat :=
  GeometricPhase.costBound (menuDepth total requestDepth dimension width) requestDepth width dimension
    (routingDepth total completed requestDepth dimension width) requestWidth

/-- A fixed circuit advances every valid encoded buffer and preserves its
geometric and request-identity invariants. Compaction adds no charged cost. -/
theorem existsCircuit
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (counts : completed + networkRecords requestDepth = total)
    (budget : 512 * total * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (targetProjection : Fin (dimension * width) → Fin requestWidth) :
    ∃ step : Circuit DeMorgan.signature
      (inputWidth completed (networkRecords requestDepth) requestWidth (2 ^ width) (dimension * width))
      (inputWidth (completed + acceptedCount requestDepth) (pendingCount requestDepth)
        requestWidth (2 ^ width) (dimension * width)),
      step.cost DeMorgan.standardCost ≤ costBound total completed requestDepth dimension width requestWidth ∧
      Transforms positive targetProjection step total := by
  let targetWires := fun (request : Fin (networkRecords requestDepth)) bit =>
    pendingWire completed (2 ^ width) (dimension * width) request (targetProjection bit)
  let sourceKeys := pointWire (completed := completed) (slots := 2 ^ width) (keyWidth := dimension * width)
    (networkRecords requestDepth) requestWidth
  let sourceFlags := flagWire (completed := completed)
    (inputWidth completed (networkRecords requestDepth) requestWidth (2 ^ width) (dimension * width))
    (PaddedLinePoints.valid positive)
  let original := pendingWire completed (2 ^ width) (dimension * width) (pending := networkRecords requestDepth)
    (requestWidth := requestWidth)
  have exactRecords := recordCount total completed requestDepth dimension width
  obtain ⟨menu, universal⟩ := GeometricPhase.existsUniversalPhase positive dimensionPositive total
    (by omega : networkRecords requestDepth ≤ total) budget targetWires sourceKeys sourceFlags original exactRecords
  let phase := GeometricPhase.circuit positive menu targetWires sourceKeys sourceFlags original exactRecords
    (acceptedCount_positive requestDepth) (acceptedCount_le requestDepth)
  let split := acceptedCount_add_pendingCount requestDepth
  refine ⟨BufferAdvance.circuit phase split, ?_, ?_⟩
  · rw [BufferAdvance.circuit_cost]
    exact GeometricPhase.circuit_cost_le positive menu targetWires sourceKeys sourceFlags original exactRecords
      (acceptedCount_positive requestDepth) (acceptedCount_le requestDepth)
  · intro data targets distinct targetDataCorrect state previous
    let input := BufferModel.input positive state data targets
    have targetEncoding : ∀ request bit, (targetWires request bit).eval input =
        binaryExtensionVectorBits positive ((state.toPhaseState targets).2 request) bit := by
      intro request bit
      rw [show targetWires request bit = pendingWire completed (2 ^ width) (dimension * width)
        request (targetProjection bit) from rfl, BufferModel.pendingWire_eval, targetDataCorrect]
      rfl
    have occupiedEncoding : MenuPointLayout.occupied sourceKeys sourceFlags input =
        (phaseOccupied (state.toPhaseState targets)).image (binaryExtensionVectorBits positive) := by
      rw [State.toPhaseState_occupied]
      exact occupied_input positive state data targets
    have originalDistinct : Function.Injective (fun request => fun bit => (original request bit).eval input) := by
      intro left right equal
      apply pendingRecord_injective state data distinct
      funext bit
      simpa only [original, input, BufferModel.pendingWire_eval, pendingRecord] using congrFun equal bit
    have correct := universal input (state.toPhaseState targets) targetEncoding occupiedEncoding originalDistinct
    rw [State.toPhaseState_occupied] at correct
    have phaseCorrect : GeometricPhase.CorrectOutput positive menu (pendingRecord state data)
        (pendingTargets state targets) (occupied state targets) (acceptedCount requestDepth)
        (phase.eval DeMorgan.interpretation input) := by
      change GeometricPhase.CorrectOutput positive menu
        (fun request bit => data (state.order (.inr request)) bit)
        (pendingTargets state targets) (occupied state targets) (acceptedCount requestDepth)
        (phase.eval DeMorgan.interpretation input)
      simpa only [original, input, BufferModel.pendingWire_eval, State.toPhaseState, phase] using correct
    exact advance_input_of_correct positive state data targets previous menu phase split phaseCorrect

end Algebraic.MassProduction.Nonuniform.BufferedPhase
