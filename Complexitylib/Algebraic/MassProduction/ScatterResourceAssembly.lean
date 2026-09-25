/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.ResourceEvaluation
public import Complexitylib.Algebraic.MassProduction.ScatterAssembly

/-!
# Scatter and resource-stage assembly

This module preserves grouped scheduler outputs while routing request
suffixes to resource slots and evaluating every shorter resource circuit.
It packages the scatter and resource bank as one independently reusable
circuit stage, before any gather or decoding work.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RoutingAssembly

open CanonicalScatter
open IncidenceRouting
open LineEnumeration
open ResourceEvaluation
open Sorting

/-! ## Sequential scatter and resource evaluation -/

/-- Preserve scheduler outputs alongside the routed scatter array. -/
noncomputable def scatterWithScheduleCircuit
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth) :=
  ((Circuit.id DeMorgan.signature
      (scheduleBitCount groups requestsPerGroup dimension width)).mapInputs
        (scatterScheduleInputIndex (totalRequests := totalRequests)
          (suffixWidth := suffixWidth))).parallel
    (scatterRoutingCircuit suffixWidth groupBitWidth capacity recordCount)

theorem scatterWithScheduleCircuit_eval
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    (scatterWithScheduleCircuit suffixWidth groupBitWidth capacity
      recordCount).eval DeMorgan.interpretation input =
      Fin.append (scatterScheduleInput input)
        (canonicalFullScatterBits widthPositive groupBitWidth capacity
          (scatterScheduleInput input) (scatterSuffixInput input)
          (fun _destination _bit => false)
          (fun _padding _bit => false) recordCount) := by
  rw [scatterWithScheduleCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_id,
    scatterRoutingCircuit_eval widthPositive]
  rfl

@[simp] theorem scatterWithScheduleCircuit_cost
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth) :
    (scatterWithScheduleCircuit suffixWidth groupBitWidth capacity
      recordCount).cost DeMorgan.standardCost =
      (CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost := by
  simp [scatterWithScheduleCircuit]

/-- Scheduler plus routed-scatter input consumed by resource evaluation. -/
@[reducible] noncomputable def resourceStageInputCount
    (groups requestsPerGroup dimension width scatterDepth groupBitWidth
      suffixWidth : Nat) : Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)

/-- Embed a scheduler bit into the combined resource-stage input. -/
noncomputable def resourceStageScheduleInputIndex
    (index : Fin (scheduleBitCount groups requestsPerGroup dimension width)) :
    Fin (resourceStageInputCount groups requestsPerGroup dimension width
      scatterDepth groupBitWidth suffixWidth) :=
  Fin.castAdd
    (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth))
    index

/-- Embed a routed-scatter bit into the combined resource-stage input. -/
noncomputable def resourceStageScatterInputIndex
    (index : Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth))) :
    Fin (resourceStageInputCount groups requestsPerGroup dimension width
      scatterDepth groupBitWidth suffixWidth) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width) index

/-- Project the scheduler portion of a combined resource-stage input. -/
noncomputable def resourceStageScheduleInput
    (input : Fin (resourceStageInputCount groups requestsPerGroup dimension
      width scatterDepth groupBitWidth suffixWidth) -> Bool) :
    Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool :=
  fun index => input (resourceStageScheduleInputIndex index)

/-- Project the routed-scatter portion of a combined resource-stage input. -/
noncomputable def resourceStageScatterInput
    (input : Fin (resourceStageInputCount groups requestsPerGroup dimension
      width scatterDepth groupBitWidth suffixWidth) -> Bool) :
    Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool :=
  fun index => input (resourceStageScatterInputIndex
    (groups := groups) (requestsPerGroup := requestsPerGroup) index)

@[simp] theorem resourceStageScheduleInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (scatter : Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool) :
    resourceStageScheduleInput (Fin.append schedule scatter) = schedule := by
  funext index
  simp [resourceStageScheduleInput, resourceStageScheduleInputIndex]

@[simp] theorem resourceStageScatterInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (scatter : Fin (networkBits scatterDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool) :
    resourceStageScatterInput (Fin.append schedule scatter) = scatter := by
  funext index
  simp [resourceStageScatterInput, resourceStageScatterInputIndex]

/-- Preserve the schedule while evaluating every shorter resource circuit in
parallel on the routed scatter output. -/
noncomputable def resourceStageCircuit
    (requestsPerGroup : Nat)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups) :=
  ((Circuit.id DeMorgan.signature
      (scheduleBitCount groups requestsPerGroup dimension width)).mapInputs
        (resourceStageScheduleInputIndex
          (scatterDepth := scatterDepth) (groupBitWidth := groupBitWidth)
          (suffixWidth := suffixWidth))).parallel
    ((resourceBankCircuit destinationFits resourceCircuits).mapInputs
      (resourceStageScatterInputIndex
        (groups := groups) (requestsPerGroup := requestsPerGroup)))

theorem resourceStageCircuit_eval
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (input : Fin (resourceStageInputCount groups requestsPerGroup dimension
      width scatterDepth groupBitWidth suffixWidth) -> Bool) :
    (resourceStageCircuit (requestsPerGroup := requestsPerGroup)
      destinationFits resourceCircuits).eval
        DeMorgan.interpretation input =
      Fin.append (resourceStageScheduleInput input)
        ((resourceBankCircuit destinationFits resourceCircuits).eval
          DeMorgan.interpretation (resourceStageScatterInput input)) := by
  rw [resourceStageCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_id, Circuit.eval_mapInputs]
  rfl

@[simp] theorem resourceStageCircuit_cost
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups) :
    (resourceStageCircuit (requestsPerGroup := requestsPerGroup)
      destinationFits resourceCircuits).cost
        DeMorgan.standardCost =
      ∑ member, (resourceCircuits member).cost DeMorgan.standardCost := by
  simp [resourceStageCircuit]

/-- Scatter, retain its schedule, and evaluate the complete resource bank. -/
noncomputable def scatterResourceCircuit
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups) :=
  (resourceStageCircuit (requestsPerGroup := requestsPerGroup)
    destinationFits resourceCircuits).comp
      (scatterWithScheduleCircuit suffixWidth groupBitWidth capacity
        recordCount)

theorem scatterResourceCircuit_eval
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool) :
    (scatterResourceCircuit suffixWidth groupBitWidth capacity recordCount
      destinationFits resourceCircuits).eval
        DeMorgan.interpretation input =
      Fin.append (scatterScheduleInput input)
        ((resourceBankCircuit destinationFits resourceCircuits).eval
          DeMorgan.interpretation
          (canonicalFullScatterBits widthPositive groupBitWidth capacity
            (scatterScheduleInput input) (scatterSuffixInput input)
            (fun _destination _bit => false)
            (fun _padding _bit => false) recordCount)) := by
  rw [scatterResourceCircuit, Circuit.eval_comp,
    resourceStageCircuit_eval, scatterWithScheduleCircuit_eval widthPositive,
    resourceStageScheduleInput_append, resourceStageScatterInput_append]

@[simp] theorem scatterResourceCircuit_cost
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords scatterDepth)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups) :
    (scatterResourceCircuit suffixWidth groupBitWidth capacity recordCount
      destinationFits resourceCircuits).cost
        DeMorgan.standardCost =
      (CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost := by
  rw [scatterResourceCircuit, Circuit.cost_comp,
    scatterWithScheduleCircuit_cost, resourceStageCircuit_cost]

end RoutingAssembly
end MassProduction
end Algebraic
