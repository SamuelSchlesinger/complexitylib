/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.GatherAssembly
public import Complexitylib.Algebraic.MassProduction.PackedPipeline
public import Complexitylib.Algebraic.MassProduction.ScatterResourceAssembly

/-!
# Complete finite pipeline assembly

This module composes scatter routing, shorter-resource evaluation, gather
routing, and decoding into one circuit whose input is an already-computed
schedule followed by the request suffixes. It proves the circuit's exact
semantics, recovery theorem, and gate-cost ledger.
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

/-! ## Complete assembled finite pipeline -/

/-- Scatter, resource evaluation, and gather as a single circuit. -/
noncomputable def scatterResourceGatherCircuit
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :=
  (gatherRoutingCircuit groupsPositive groupBitWidth orderWidth
    incidenceFits capacity gatherRecordCount).comp
      (scatterResourceCircuit suffixWidth groupBitWidth capacity
        scatterRecordCount scatterDestinationFits resourceCircuits)

/-- The exact gate count of `scatterResourceGatherCircuit`. -/
@[simp] theorem scatterResourceGatherCircuit_size
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth orderWidth incidenceFits
      capacity scatterRecordCount scatterDestinationFits resourceCircuits gatherRecordCount).size =
      (scatterResourceCircuit suffixWidth groupBitWidth capacity
            scatterRecordCount scatterDestinationFits resourceCircuits).size +
        (gatherRoutingCircuit groupsPositive groupBitWidth orderWidth
            incidenceFits capacity gatherRecordCount).size := by
  simp [scatterResourceGatherCircuit]

theorem scatterResourceGatherCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool) :
    (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      scatterDestinationFits resourceCircuits
      gatherRecordCount).eval DeMorgan.interpretation input =
      let schedule := scatterScheduleInput input
      let scatterOutput := canonicalFullScatterBits widthPositive
        groupBitWidth capacity schedule (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) scatterRecordCount
      let bankOutput :=
        (resourceBankCircuit scatterDestinationFits
          resourceCircuits).eval DeMorgan.interpretation scatterOutput
      canonicalGatherBits widthPositive groupBitWidth orderWidth incidenceFits
        capacity schedule
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          bankOutput)
        (fun _destination _bit => false)
        (fun _padding _bit => false) gatherRecordCount := by
  rw [scatterResourceGatherCircuit, Circuit.eval_comp,
    gatherRoutingCircuit_eval groupsPositive widthPositive,
    scatterResourceCircuit_eval widthPositive,
    gatherScheduleInput_append, gatherBankInput_append]

@[simp] theorem scatterResourceGatherCircuit_cost
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      scatterDestinationFits resourceCircuits
      gatherRecordCount).cost DeMorgan.standardCost =
      ((CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost := by
  rw [scatterResourceGatherCircuit, Circuit.cost_comp,
    scatterResourceCircuit_cost, gatherRoutingCircuit_cost]

/-- The complete scatter-evaluate-gather-decode circuit on an already
computed schedule and its request suffixes.  Both sorter-capacity inclusions
are derived from the exact padding equations, so callers do not supply
redundant proof arguments. -/
noncomputable def assembledPipelineCircuit
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
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
  let scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth := by
    rw [← scatterRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  let gatherDestinationFits :
      totalRequests * nonzeroScalarCount width <=
        networkRecords gatherDepth := by
    rw [← gatherRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  (GatherDecoder.circuit
    (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
    (metadataWidth := orderWidth + 1)
    gatherDestinationFits
    (fun request => (placement (requestSource request)).2)).comp
      (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount
        scatterDestinationFits resourceCircuits gatherRecordCount)

/-- The assembled pipeline has exactly the gates of scatter, resource evaluation and gather,
followed by one fixed decoder per request. -/
@[simp] theorem assembledPipelineCircuit_size
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
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
    (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth orderWidth incidenceFits
      capacity placement requestSource scatterRecordCount resourceCircuits gatherRecordCount).size =
      (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
            orderWidth incidenceFits capacity scatterRecordCount
            (by rw [← scatterRecordCount]; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
            resourceCircuits gatherRecordCount).size +
        ∑ request : Fin totalRequests,
          GatherDecoder.decoderGateCount (width := width) (depth := gatherDepth)
            (incidenceKeyWidth groupBitWidth dimension width) (orderWidth + 1)
            (by rw [← gatherRecordCount]; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
            (fun request => (placement (requestSource request)).2) request := by
  simp [assembledPipelineCircuit]

theorem assembledPipelineCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
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
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool) :
    (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity placement requestSource
      scatterRecordCount resourceCircuits gatherRecordCount).eval
        DeMorgan.interpretation input =
      let scatterDestinationFits :
          2 ^ (groupBitWidth + dimension * width) <=
            networkRecords scatterDepth := by
        rw [← scatterRecordCount]
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      let gatherDestinationFits :
          totalRequests * nonzeroScalarCount width <=
            networkRecords gatherDepth := by
        rw [← gatherRecordCount]
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      let schedule := scatterScheduleInput input
      let scatterOutput := canonicalFullScatterBits widthPositive
        groupBitWidth capacity schedule (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) scatterRecordCount
      let bankOutput :=
        (resourceBankCircuit scatterDestinationFits
          resourceCircuits).eval DeMorgan.interpretation scatterOutput
      let gatherOutput := canonicalGatherBits widthPositive groupBitWidth
        orderWidth incidenceFits capacity schedule
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          bankOutput)
        (fun _destination _bit => false)
        (fun _padding _bit => false) gatherRecordCount
      (GatherDecoder.circuit
        (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
        (metadataWidth := orderWidth + 1)
        gatherDestinationFits
        (fun request => (placement (requestSource request)).2)).eval
          DeMorgan.interpretation gatherOutput := by
  rw [assembledPipelineCircuit, Circuit.eval_comp,
    scatterResourceGatherCircuit_eval groupsPositive widthPositive]

set_option maxHeartbeats 1500000 in
/-- End-to-end correctness of the single assembled finite circuit.  Given
the geometric scheduler invariants and correct shorter-resource circuits, it
returns every requested Boolean value in its original request position. -/
theorem assembledPipelineCircuit_recovers
    (widthPositive : 0 < width)
    (dimensionPositive : 0 < dimension)
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth) -> Bool)
    (directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : forall request scalar,
      requestScheduledLinePoint widthPositive capacity
          (scatterScheduleInput input) request scalar =
        packedTargetPoint widthPositive placement (requestSource request) +
          enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector (directions request).rep)
    (setFormula : forall request,
      requestScheduledLineSet widthPositive capacity
          (scatterScheduleInput input) request =
        ForbiddenRanks.binaryExtensionPuncturedLine
          (packedTargetPoint widthPositive placement (requestSource request))
          (directions request))
    (withinGroupDisjoint : forall left right,
      (requestGroupSlot capacity left).1 =
          (requestGroupSlot capacity right).1 ->
      left ≠ right ->
        Disjoint
          (requestScheduledLineSet widthPositive capacity
            (scatterScheduleInput input) left)
          (requestScheduledLineSet widthPositive capacity
            (scatterScheduleInput input) right))
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
        networkRecords gatherDepth) :
    (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity placement requestSource
      scatterRecordCount resourceCircuits gatherRecordCount).eval
        DeMorgan.interpretation input =
      fun request => function (requestSource request)
        (scatterSuffixInput input request) := by
  rw [assembledPipelineCircuit_eval groupsPositive widthPositive]
  let schedule := scatterScheduleInput input
  let requestSuffix := scatterSuffixInput input
  have recovered := scatter_evaluate_gather_decode_recovers widthPositive
    dimensionPositive groupsPositive groupFits incidenceFits capacity schedule
    placement function requestSource requestSuffix directions pointFormula
    setFormula withinGroupDisjoint
    (fun _destination _bit => false)
    (fun _padding _bit => false) scatterRecordCount
    resourceCircuits computes
    (fun _destination _bit => false)
    (fun _padding _bit => false) gatherRecordCount
  simpa only [evaluatedResourceValues] using recovered

/-- Exact cost ledger for the assembled finite circuit.  Record assembly,
schedule preservation, and all fixed reindexings contribute zero gates. -/
@[simp] theorem assembledPipelineCircuit_cost
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (requestSource : Fin totalRequests -> Prefix)
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
    (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity placement requestSource
      scatterRecordCount resourceCircuits gatherRecordCount).cost
        DeMorgan.standardCost =
      (((CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
        ∑ member, (resourceCircuits member).cost
          DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost) +
      totalRequests * (nonzeroScalarCount width * 4) := by
  unfold assembledPipelineCircuit
  rw [Circuit.cost_comp, scatterResourceGatherCircuit_cost,
    GatherDecoder.circuit_cost]

end RoutingAssembly
end MassProduction
end Algebraic
