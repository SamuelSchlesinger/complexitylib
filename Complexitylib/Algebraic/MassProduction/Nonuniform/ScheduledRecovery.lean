/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.SchedulerCircuit
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferResourceEvaluation
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RestoreRequestOrder

/-!
# Complete high-rate recovery from encoded request metadata

One circuit schedules arbitrary repeated targets, evaluates the exact
resource bank, recovers each requested source bit, and restores the original
request order. Copy, information-point, basis-bit, and suffix metadata are
read from supplied wires. An offline prefix lookup can supply these wires.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.ScheduledRecovery

open Sorting BufferInput BufferModel HighRate
open scoped LinearAlgebra.Projectivization

variable {Source : Type*}

set_option backward.isDefEq.respectTransparency false

/-- Total overhead excluding the exact bank evaluation cost. -/
def overhead (depth copies dimension width payloadWidth copyBits selectorBits suffixWidth : Nat) : Nat :=
  networkRecords depth * 2 ^ width *
    BufferIteration.polynomialFactor (networkRecords depth) dimension width (depth + payloadWidth) +
  IncidenceEvaluation.routingCost (networkRecords depth * 2 ^ width) (ResourceLayout.count copies dimension width)
    (ResourceLayout.keyWidth copyBits dimension width selectorBits) suffixWidth +
  networkRecords depth * 2 ^ width * 4 +
  256 * (networkRecords depth + networkRecords depth + 1) *
    (FiniteParameters.binaryDepth (networkRecords depth + networkRecords depth + 1) + depth + 1 + 2) ^ 5

/-- The complete scheduler/resource/recovery circuit computes every source
request in its original order. There is no input-dependent circuit choice
and no distinctness premise on the targets, prefixes, or suffixes. -/
theorem existsCircuit
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies)
    (function : Source → (Fin suffixWidth → Bool) → Bool)
    (copyFits : copies ≤ 2 ^ copyBits) (selectorFits : width ≤ 2 ^ selectorBits)
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (targetProjection : Fin (dimension * width) → Fin payloadWidth)
    (copyProjection : Fin copyBits → Fin payloadWidth)
    (selectorProjection : Fin selectorBits → Fin payloadWidth)
    (suffixProjection : Fin suffixWidth → Fin payloadWidth)
    (members : (resource : Fin (ResourceLayout.count copies dimension width)) →
      Circuit DeMorgan.signature suffixWidth 1)
    (membersCorrect : ∀ resource suffix,
      (members resource).eval DeMorgan.interpretation suffix 0 =
        ResourceLayout.function positive code placement function resource suffix) :
    ∃ result : Circuit DeMorgan.signature inputs (networkRecords depth),
      result.cost DeMorgan.standardCost ≤
        overhead depth copies dimension width payloadWidth copyBits selectorBits suffixWidth +
          ∑ resource, (members resource).cost DeMorgan.standardCost ∧
      ∀ (input : Fin inputs → Bool) (sources : Fin (networkRecords depth) → Source)
        (suffixes : Fin (networkRecords depth) → Fin suffixWidth → Bool),
        (∀ request bit, (original request (targetProjection bit)).eval input =
          binaryExtensionVectorBits positive (placement (sources request)).2.1.val bit) →
        (∀ request bit, (original request (copyProjection bit)).eval input =
          finiteIndexBits copyBits (placement (sources request)).1 bit) →
        (∀ request bit, (original request (selectorProjection bit)).eval input =
          finiteIndexBits selectorBits (placement (sources request)).2.2 bit) →
        (∀ request bit, (original request (suffixProjection bit)).eval input = suffixes request bit) →
        ∀ request, result.eval DeMorgan.interpretation input request = function (sources request) (suffixes request) := by
  obtain ⟨schedule, scheduleBound, scheduleCorrect⟩ := Scheduler.existsCircuit
    positive dimensionPositive budget original targetProjection
  obtain ⟨recovery, recoveryBound, recoveryCorrect⟩ := BufferResourceEvaluation.existsCircuit
    (total := networkRecords depth) positive code placement function copyFits selectorFits
    (fun bit => Fin.natAdd depth (copyProjection bit))
    (fun bit => Fin.natAdd depth (selectorProjection bit))
    (fun bit => Fin.natAdd depth (suffixProjection bit)) members membersCorrect
  let identifiers := fun (request : Fin (networkRecords depth)) (bit : Fin depth) => PreparedInputs.original (networkRecords depth)
    (BufferResourceWires.dataWire (2 ^ width) (dimension * width) request (Fin.castAdd payloadWidth bit))
  obtain ⟨restore, restoreBound, restoreCorrect⟩ := RestoreRequestOrder.existsCircuit
    (PowerLayout.codes depth) (PowerLayout.codes_injective depth) identifiers
    (PreparedInputs.output (inputWidth (networkRecords depth) 0 (depth + payloadWidth) (2 ^ width) (dimension * width)))
  refine ⟨restore.comp ((PreparedInputs.circuit recovery).comp schedule), ?_, ?_⟩
  · rw [Circuit.cost_comp, Circuit.cost_comp, PreparedInputs.circuit_cost]
    have combined := Nat.add_le_add (Nat.add_le_add scheduleBound recoveryBound) restoreBound
    exact combined.trans_eq (by unfold overhead; ring)
  · intro input sources suffixes targetCorrect copyCorrect selectorCorrect suffixCorrect request
    let targets := BufferResourceEvaluation.targets code placement sources
    obtain ⟨state, scheduleOutput, scheduled⟩ := scheduleCorrect input targets targetCorrect
    let buffer := BufferModel.input positive state (TaggedBuffer.data original input) targets
    have recovered : ∀ position, recovery.eval DeMorgan.interpretation buffer position =
        function (sources (state.order (.inl position))) (suffixes (state.order (.inl position))) := by
      apply recoveryCorrect (TaggedBuffer.data original input) sources suffixes state scheduled
      · intro position bit
        rw [TaggedBuffer.data_payload, copyCorrect]
      · intro position bit
        rw [TaggedBuffer.data_payload, selectorCorrect]
      · intro position bit
        rw [TaggedBuffer.data_payload, suffixCorrect]
    have identifiersCorrect : ∀ position bit, (identifiers position bit).eval
        ((PreparedInputs.circuit recovery).eval DeMorgan.interpretation buffer) =
          PowerLayout.codes depth (state.finishedOrder position) bit := by
      intro position bit
      rw [PreparedInputs.original_eval, BufferResourceWires.dataWire_eval]
      exact Fin.append_left _ _ bit
    have restored := restoreCorrect ((PreparedInputs.circuit recovery).eval DeMorgan.interpretation buffer)
      state.finishedOrder identifiersCorrect (state.finishedOrder.symm request)
    rw [Equiv.apply_symm_apply, PreparedInputs.output_eval, recovered,
      ← State.finishedOrder_apply, Equiv.apply_symm_apply] at restored
    rw [Circuit.eval_comp, Circuit.eval_comp, scheduleOutput]
    exact restored

end Algebraic.MassProduction.Nonuniform.ScheduledRecovery
