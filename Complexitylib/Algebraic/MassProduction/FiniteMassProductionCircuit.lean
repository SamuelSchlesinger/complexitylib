/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.PipelineAssembly

/-!
# Complete finite mass-production circuit

This module hardwires packed target points into the grouped scheduler, keeps
request suffixes as the only runtime inputs, and composes that front end with
the complete scatter-evaluate-gather-decode pipeline. It proves end-to-end
recovery and the exact top-level gate-cost ledger.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RoutingAssembly

universe u

variable {Prefix : Type u}

open scoped LinearAlgebra.Projectivization
open GroupedScheduler
open CanonicalMetadataRouting
open CanonicalScatter
open GatherRouting
open IncidenceRouting
open LineEnumeration
open PackedPipeline
open ResourceEvaluation
open SchedulerIteration
open Sorting

/-! ## Hardwired grouped scheduling -/

/-- Assemble a fixed rectangular target family for the grouped scheduler.
The suffix inputs are deliberately ignored by this zero-cost layer. -/
noncomputable def fixedGroupedTargetAssemblyCircuit
    (totalRequests : Nat)
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :=
  DeMorgan.Wiring.circuit (inputs := totalRequests * suffixWidth) fun output =>
    .constant (groupedTargetArrayBits widthPositive targets output)

/-- Every output bit is a hardwired constant: exactly one constant gate per output bit and no other
gates. -/
@[simp] theorem fixedGroupedTargetAssemblyCircuit_size
    (totalRequests : Nat)
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :
    (fixedGroupedTargetAssemblyCircuit totalRequests suffixWidth widthPositive targets).size =
      groups * (requestsPerGroup * pointBitWidth dimension width) := by
  simp [fixedGroupedTargetAssemblyCircuit, DeMorgan.Wiring.expression]

@[simp] theorem fixedGroupedTargetAssemblyCircuit_cost
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive targets).cost DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

theorem fixedGroupedTargetAssemblyCircuit_eval
    (suffixWidth : Nat)
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive targets).eval DeMorgan.interpretation input =
      groupedTargetArrayBits widthPositive targets := by
  rw [fixedGroupedTargetAssemblyCircuit, DeMorgan.Wiring.circuit_eval]
  rfl

/-- Run the grouped greedy scheduler on hardwired packed target points while
passing every runtime suffix bit through unchanged. -/
noncomputable def fixedScheduleAndSuffixCircuit
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  let groupSize := requestGroupSize totalRequests groups
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  let targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width :=
    fun request => packedTargetPoint widthPositive placement
      (requestSource request)
  let paddedTargets : Fin groups -> Fin groupSize ->
      Fin dimension -> BinaryExtension width :=
    paddedGroupedTargets capacity targets dummyTarget
  ((groupedScheduleCircuit dimension widthPositive schedulerDepth groups
      groupSize allFit).comp
    (fixedGroupedTargetAssemblyCircuit (totalRequests := totalRequests)
      suffixWidth widthPositive paddedTargets)).parallel
    (Circuit.id DeMorgan.signature (totalRequests * suffixWidth))

/-- The exact gate count of `fixedScheduleAndSuffixCircuit`. -/
@[simp] theorem fixedScheduleAndSuffixCircuit_size
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (fixedScheduleAndSuffixCircuit widthPositive groupsPositive schedulerDepth suffixWidth allFit
      placement requestSource dummyTarget).size =
      (fixedGroupedTargetAssemblyCircuit totalRequests suffixWidth widthPositive
            (paddedGroupedTargets (requestGroupCapacity groupsPositive)
              (fun request =>
                packedTargetPoint widthPositive placement (requestSource request))
              dummyTarget)).size +
        groups *
          greedyScheduleGateCount dimension widthPositive schedulerDepth
            (requestGroupSize totalRequests groups) := by
  simp [fixedScheduleAndSuffixCircuit]

theorem fixedScheduleAndSuffixCircuit_eval
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (fixedScheduleAndSuffixCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth allFit placement requestSource dummyTarget).eval
        DeMorgan.interpretation input =
      let groupSize := requestGroupSize totalRequests groups
      let capacity := requestGroupCapacity
        (totalRequests := totalRequests) groupsPositive
      let targets : Fin totalRequests ->
          Fin dimension -> BinaryExtension width :=
        fun request => packedTargetPoint widthPositive placement
          (requestSource request)
      let paddedTargets : Fin groups -> Fin groupSize ->
          Fin dimension -> BinaryExtension width :=
        paddedGroupedTargets capacity targets dummyTarget
      Fin.append
        (groupedScheduleOutput dimension widthPositive schedulerDepth groups
          groupSize allFit paddedTargets)
        input := by
  unfold fixedScheduleAndSuffixCircuit
  rw [Circuit.eval_parallel, Circuit.eval_comp,
    fixedGroupedTargetAssemblyCircuit_eval, Circuit.eval_id]
  rfl

@[simp] theorem fixedScheduleAndSuffixCircuit_cost
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (fixedScheduleAndSuffixCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth allFit placement requestSource dummyTarget).cost
        DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost := by
  simp [fixedScheduleAndSuffixCircuit]

/-- The complete finite mass-production circuit.  Its only runtime inputs
are the row-major suffixes; selected function prefixes, packed target points,
and the dummy padding target are nonuniform construction data. -/
noncomputable def finiteMassProductionCircuit
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :=
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
    orderWidth incidenceFits capacity placement requestSource
    scatterRecordCount resourceCircuits gatherRecordCount).comp
      (fixedScheduleAndSuffixCircuit widthPositive groupsPositive
        schedulerDepth suffixWidth allFit placement requestSource dummyTarget)

/-- The exact gate count of `finiteMassProductionCircuit`. -/
@[simp] theorem finiteMassProductionCircuit_size
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (finiteMassProductionCircuit widthPositive groupsPositive schedulerDepth suffixWidth
      groupBitWidth orderWidth allFit incidenceFits placement requestSource dummyTarget
      scatterRecordCount resourceCircuits gatherRecordCount).size =
      (fixedScheduleAndSuffixCircuit widthPositive groupsPositive schedulerDepth
            suffixWidth allFit placement requestSource dummyTarget).size +
        (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
            orderWidth incidenceFits (requestGroupCapacity groupsPositive)
            placement requestSource scatterRecordCount resourceCircuits
            gatherRecordCount).size := by
  simp [finiteMassProductionCircuit]

theorem finiteMassProductionCircuit_eval
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (finiteMassProductionCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth groupBitWidth orderWidth allFit incidenceFits placement
      requestSource dummyTarget scatterRecordCount resourceCircuits
      gatherRecordCount).eval DeMorgan.interpretation input =
      let groupSize := requestGroupSize totalRequests groups
      let capacity := requestGroupCapacity
        (totalRequests := totalRequests) groupsPositive
      let targets : Fin totalRequests ->
          Fin dimension -> BinaryExtension width :=
        fun request => packedTargetPoint widthPositive placement
          (requestSource request)
      let paddedTargets : Fin groups -> Fin groupSize ->
          Fin dimension -> BinaryExtension width :=
        paddedGroupedTargets capacity targets dummyTarget
      let schedule := groupedScheduleOutput dimension widthPositive
        schedulerDepth groups groupSize allFit paddedTargets
      (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity placement requestSource
        scatterRecordCount resourceCircuits gatherRecordCount).eval
          DeMorgan.interpretation (Fin.append schedule input) := by
  rw [finiteMassProductionCircuit, Circuit.eval_comp,
    fixedScheduleAndSuffixCircuit_eval]

set_option maxHeartbeats 1800000 in
/-- The fully assembled circuit, including the verified deterministic grouped
scheduler, computes the requested functions on all row-major suffix inputs. -/
theorem finiteMassProductionCircuit_recovers
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction widthPositive placement function point bit)
          groups))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (totalRequests * suffixWidth) -> Bool) :
    (finiteMassProductionCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth groupBitWidth orderWidth allFit incidenceFits placement
      requestSource dummyTarget scatterRecordCount resourceCircuits
      gatherRecordCount).eval DeMorgan.interpretation input =
      fun request => function (requestSource request)
        (fun bit => input (finProdFinEquiv (request, bit))) := by
  rw [finiteMassProductionCircuit_eval,
    assembledPipelineCircuit_eval groupsPositive widthPositive,
    scatterScheduleInput_append, scatterSuffixInput_append]
  let requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool :=
    fun request bit => input (finProdFinEquiv (request, bit))
  have recovered := grouped_scatter_evaluate_gather_decode_recovers
    (width := width) (dimension := dimension) (groups := groups)
    (totalRequests := totalRequests) (groupBitWidth := groupBitWidth)
    (orderWidth := orderWidth) (schedulerDepth := schedulerDepth)
    (suffixWidth := suffixWidth) (scatterDepth := scatterDepth)
    (scatterPaddingCount := scatterPaddingCount)
    (gatherDepth := gatherDepth) (gatherPaddingCount := gatherPaddingCount)
    widthPositive widthAtLeastTwo dimensionPositive groupsPositive groupFits
    incidenceFits allFit directionCapacity placement function requestSource
    requestSuffix dummyTarget
    (fun _destination _bit => false)
    (fun _padding _bit => false) scatterRecordCount
    resourceCircuits computes
    (fun _destination _bit => false)
    (fun _padding _bit => false) gatherRecordCount
  simpa only [evaluatedResourceValues] using recovered

/-- Exact top-level finite cost ledger: scheduler, scatter routing, shorter
resource bank, gather routing, and decoder. -/
@[simp] theorem finiteMassProductionCircuit_cost
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (finiteMassProductionCircuit widthPositive groupsPositive schedulerDepth
      suffixWidth groupBitWidth orderWidth allFit incidenceFits placement
      requestSource dummyTarget scatterRecordCount resourceCircuits
      gatherRecordCount).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost +
      ((((CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost) +
      totalRequests * (nonzeroScalarCount width * 4)) := by
  unfold finiteMassProductionCircuit
  rw [Circuit.cost_comp, fixedScheduleAndSuffixCircuit_cost,
    assembledPipelineCircuit_cost]

end RoutingAssembly
end MassProduction
end Algebraic
