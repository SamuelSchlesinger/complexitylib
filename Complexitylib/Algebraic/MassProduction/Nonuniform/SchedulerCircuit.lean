/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.TaggedBuffer

/-!
# A complete nonuniform near-linear geometric scheduler

For a power-of-two batch, one fixed circuit accepts arbitrary request
payloads with encoded geometric targets. It adds distinct identifiers,
executes every halving phase, and returns all payloads and disjoint recovery
point lists. Menu choices precede the input. Repeated targets are allowed.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Scheduler

open Sorting BufferInput BufferModel
open scoped LinearAlgebra.Projectivization

/-- A fixed circuit schedules the entire batch with a cost linear in the
number of request/scalar pairs, up to the displayed polynomial factor.
The output model retains exact original identities and request payloads. -/
theorem existsCircuit
    (positive : 0 < width) (dimensionPositive : 0 < dimension)
    (budget : 512 * networkRecords depth * Nat.card (BinaryExtension width) ≤
      Nat.card (ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)))
    (original : Fin (networkRecords depth) → Fin payloadWidth → DeMorgan.Wiring inputs)
    (targetProjection : Fin (dimension * width) → Fin payloadWidth) :
    ∃ scheduler : Circuit DeMorgan.signature inputs
      (inputWidth (networkRecords depth) 0 (depth + payloadWidth) (2 ^ width) (dimension * width)),
      scheduler.cost DeMorgan.standardCost ≤ networkRecords depth * 2 ^ width *
        BufferIteration.polynomialFactor (networkRecords depth) dimension width (depth + payloadWidth) ∧
      ∀ (input : Fin inputs → Bool)
        (targets : Fin (networkRecords depth) → Fin dimension → BinaryExtension width),
        (∀ request bit, (original request (targetProjection bit)).eval input =
          binaryExtensionVectorBits positive (targets request) bit) →
        ∃ state : State (networkRecords depth) (networkRecords depth) 0 dimension width,
          scheduler.eval DeMorgan.interpretation input =
            BufferModel.input positive state (TaggedBuffer.data original input) targets ∧
          WellScheduled state targets := by
  obtain ⟨iteration, bound, correct⟩ := BufferIteration.existsCircuit_linear
    positive dimensionPositive (Nat.zero_add (networkRecords depth)) budget
    (fun bit => Fin.natAdd depth (targetProjection bit))
  refine ⟨iteration.comp (TaggedBuffer.circuit dimension width original), ?_, ?_⟩
  · rw [Circuit.cost_comp, TaggedBuffer.circuit_cost, Nat.zero_add]
    exact bound
  · intro input targets targetCorrect
    obtain ⟨state, output, valid⟩ := correct (TaggedBuffer.data original input) targets
      (TaggedBuffer.data_injective original input)
      (fun request bit => (TaggedBuffer.data_payload original input request (targetProjection bit)).trans
        (targetCorrect request bit))
      (State.initial (networkRecords depth) dimension width) (State.initial_wellScheduled targets)
    refine ⟨state, ?_, valid⟩
    rw [Circuit.eval_comp, TaggedBuffer.circuit_eval positive original input targets, output]

end Algebraic.MassProduction.Nonuniform.Scheduler
