/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.GatherDecoder
public import Complexitylib.Algebraic.MassProduction.PackedGroupedRecovery
public import Complexitylib.Algebraic.MassProduction.ResourceEvaluation

/-!
# Exact packed scatter-evaluate-gather-decode pipeline

This module composes the finite correctness interfaces.  It assumes one
supplied `groups`-copy circuit for each shorter Boolean resource function,
wires them to canonical scatter slots, gathers the resulting field values
back to fixed incidence records, and applies the fixed XOR decoder.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace PackedPipeline

universe u

variable {Prefix : Type u}

open scoped BigOperators LinearAlgebra.Projectivization
open CanonicalScatter
open GatherDecoder
open GatherRouting
open GroupedRecovery
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open PackedGroupedRecovery
open ResourceEvaluation
open RoutingMetadata
open SchedulerIteration
open Sorting

set_option maxHeartbeats 1000000 in
/-- Scatter, shorter-resource evaluation, and gather return every incidence's
complete encoded field value on its literal row-major output record. -/
theorem gather_evaluatedPackedResources_routes_incidence
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : forall request scalar,
      requestScheduledLinePoint widthPositive capacity scheduleOutput
          request scalar =
        targets request + enumeratedNonzeroScalar scalar •
          normalizeBinaryExtensionVector (directions request).rep)
    (withinGroupDisjoint : forall left right,
      (requestGroupSlot capacity left).1 =
          (requestGroupSlot capacity right).1 ->
      left ≠ right ->
        Disjoint
          (requestScheduledLineSet widthPositive capacity scheduleOutput left)
          (requestScheduledLineSet widthPositive capacity scheduleOutput right))
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool)
    (scatterDestinationSuffix :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin suffixWidth -> Bool)
    (scatterPaddingSuffix : Fin scatterPaddingCount ->
      Fin suffixWidth -> Bool)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction widthPositive placement function point bit)
          groups))
    (gatherDestinationValues :
      Fin (totalRequests * nonzeroScalarCount width) -> Fin width -> Bool)
    (gatherPaddingValues : Fin gatherPaddingCount -> Fin width -> Bool)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
      capacity scheduleOutput requestSuffix scatterDestinationSuffix
      scatterPaddingSuffix scatterRecordCount
    let scatterDestinationFits :
        2 ^ (groupBitWidth + dimension * width) <=
          networkRecords scatterDepth := by
      rw [← scatterRecordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    let resourceValues := evaluatedResourceValues groupsPositive
      groupBitWidth dimension width scatterDepth suffixWidth
      scatterDestinationFits gateCounts resourceCircuits scatterOutput
    let gatherOutput := canonicalGatherBits widthPositive groupBitWidth
      orderWidth incidenceFits capacity scheduleOutput resourceValues
      gatherDestinationValues gatherPaddingValues gatherRecordCount
    let gatherDestinationFits :
        totalRequests * nonzeroScalarCount width <=
          networkRecords gatherDepth := by
      rw [← gatherRecordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    recordValue gatherOutput
        (Fin.castLE gatherDestinationFits incidence) =
      fun bit => decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function
          (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
            incidence).2
          (requestSuffix (incidenceAt incidence).1)) bit := by
  dsimp only
  let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
    capacity scheduleOutput requestSuffix scatterDestinationSuffix
    scatterPaddingSuffix scatterRecordCount
  have scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth := by
    rw [← scatterRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  let resourceValues := evaluatedResourceValues groupsPositive
    groupBitWidth dimension width scatterDepth suffixWidth
    scatterDestinationFits gateCounts resourceCircuits scatterOutput
  let gatherOutput := canonicalGatherBits widthPositive groupBitWidth
    orderWidth incidenceFits capacity scheduleOutput resourceValues
    gatherDestinationValues gatherPaddingValues gatherRecordCount
  have gathered := canonicalGatherBits_routes_incidence widthPositive
    groupFits incidenceFits capacity scheduleOutput targets directions
    pointFormula withinGroupDisjoint resourceValues gatherDestinationValues
    gatherPaddingValues gatherRecordCount incidence
  dsimp only at gathered
  have evaluated := evaluatedResourceValues_routes_incidence widthPositive
    groupsPositive groupFits capacity scheduleOutput targets directions
    pointFormula withinGroupDisjoint requestSuffix scatterDestinationSuffix
    scatterPaddingSuffix scatterRecordCount gateCounts resourceCircuits
    (packedResourceFunction widthPositive placement function) computes
    incidence
  dsimp only at evaluated
  have packed :
      (fun bit => packedResourceFunction widthPositive placement function
        (scheduledIncidencePointIndex widthPositive capacity scheduleOutput
          incidence) bit
        (requestSuffix (incidenceAt incidence).1)) =
      (fun bit => decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function
          (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
            incidence).2
          (requestSuffix (incidenceAt incidence).1)) bit) := by
    funext bit
    exact packedResourceFunction_scheduledIncidencePoint widthPositive
      capacity scheduleOutput placement function incidence bit
      (requestSuffix (incidenceAt incidence).1)
  exact gathered.trans (evaluated.trans packed)

set_option maxHeartbeats 800000 in
/-- Once the fixed gather invariant is available, the explicit XOR circuit
recovers all requested Boolean values in request order. -/
theorem decoder_recovers_of_gatheredPackedResources
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool)
    (gatherOutput : Fin (networkBits gatherDepth
      (recordWidth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width)) -> Bool)
    (gatherDestinationFits :
      totalRequests * nonzeroScalarCount width <=
        networkRecords gatherDepth)
    (gatherCorrect : forall incidence,
      recordValue gatherOutput
          (Fin.castLE gatherDestinationFits incidence) =
        fun bit => decodeBinaryExtension widthPositive
          (packedEvaluationResource widthPositive placement function
            (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
              incidence).2
            (requestSuffix (incidenceAt incidence).1)) bit)
    (lineRecovers : forall request,
      (∑ scalar, decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function
          (requestScheduledLinePoint widthPositive capacity scheduleOutput
            request scalar)
          (requestSuffix request))
        (placement (requestSource request)).2) =
      function (requestSource request) (requestSuffix request)) :
    (GatherDecoder.circuit
        (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
        (metadataWidth := orderWidth + 1)
        gatherDestinationFits
        (fun request => (placement (requestSource request)).2)).eval
        DeMorgan.interpretation gatherOutput =
      fun request => function (requestSource request)
        (requestSuffix request) := by
  let incidenceValue := fun incidence =>
    fun bit => decodeBinaryExtension widthPositive
      (packedEvaluationResource widthPositive placement function
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          incidence).2
        (requestSuffix (incidenceAt incidence).1)) bit
  apply GatherDecoder.circuit_recovers gatherDestinationFits
    (fun request => (placement (requestSource request)).2)
    gatherOutput incidenceValue
    (fun request => function (requestSource request) (requestSuffix request))
    gatherCorrect
  intro request
  simpa only [incidenceValue, incidenceAt_finProdFinEquiv,
    scheduledIncidenceSlotAt_finProdFinEquiv_second] using
      lineRecovers request

set_option maxHeartbeats 1500000 in
/-- Finite end-to-end correctness of the exact manuscript pipeline.  Under
the scheduler's geometric invariants and correct shorter-resource circuits,
the explicit fixed-wire decoder returns every requested value of `function`.
-/
theorem scatter_evaluate_gather_decode_recovers
    (widthPositive : 0 < width)
    (dimensionPositive : 0 < dimension)
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool)
    (directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : forall request scalar,
      requestScheduledLinePoint widthPositive capacity scheduleOutput
          request scalar =
        packedTargetPoint widthPositive placement (requestSource request) +
          enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector (directions request).rep)
    (setFormula : forall request,
      requestScheduledLineSet widthPositive capacity scheduleOutput request =
        ForbiddenRanks.binaryExtensionPuncturedLine
          (packedTargetPoint widthPositive placement (requestSource request))
          (directions request))
    (withinGroupDisjoint : forall left right,
      (requestGroupSlot capacity left).1 =
          (requestGroupSlot capacity right).1 ->
      left ≠ right ->
        Disjoint
          (requestScheduledLineSet widthPositive capacity scheduleOutput left)
          (requestScheduledLineSet widthPositive capacity scheduleOutput right))
    (scatterDestinationSuffix :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin suffixWidth -> Bool)
    (scatterPaddingSuffix : Fin scatterPaddingCount ->
      Fin suffixWidth -> Bool)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction widthPositive placement function point bit)
          groups))
    (gatherDestinationValues :
      Fin (totalRequests * nonzeroScalarCount width) -> Fin width -> Bool)
    (gatherPaddingValues : Fin gatherPaddingCount -> Fin width -> Bool)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
      capacity scheduleOutput requestSuffix scatterDestinationSuffix
      scatterPaddingSuffix scatterRecordCount
    let scatterDestinationFits :
        2 ^ (groupBitWidth + dimension * width) <=
          networkRecords scatterDepth := by
      rw [← scatterRecordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    let resourceValues := evaluatedResourceValues groupsPositive
      groupBitWidth dimension width scatterDepth suffixWidth
      scatterDestinationFits gateCounts resourceCircuits scatterOutput
    let gatherOutput := canonicalGatherBits widthPositive groupBitWidth
      orderWidth incidenceFits capacity scheduleOutput resourceValues
      gatherDestinationValues gatherPaddingValues gatherRecordCount
    let gatherDestinationFits :
        totalRequests * nonzeroScalarCount width <=
          networkRecords gatherDepth := by
      rw [← gatherRecordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    (GatherDecoder.circuit
        (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
        (metadataWidth := orderWidth + 1)
        gatherDestinationFits
        (fun request => (placement (requestSource request)).2)).eval
        DeMorgan.interpretation gatherOutput =
      fun request => function (requestSource request)
        (requestSuffix request) := by
  dsimp only
  let targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width :=
    fun request => packedTargetPoint widthPositive placement
      (requestSource request)
  let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
    capacity scheduleOutput requestSuffix scatterDestinationSuffix
    scatterPaddingSuffix scatterRecordCount
  have scatterDestinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords scatterDepth := by
    rw [← scatterRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  let resourceValues := evaluatedResourceValues groupsPositive
    groupBitWidth dimension width scatterDepth suffixWidth
    scatterDestinationFits gateCounts resourceCircuits scatterOutput
  let gatherOutput := canonicalGatherBits widthPositive groupBitWidth
    orderWidth incidenceFits capacity scheduleOutput resourceValues
    gatherDestinationValues gatherPaddingValues gatherRecordCount
  have gatherDestinationFits :
      totalRequests * nonzeroScalarCount width <=
        networkRecords gatherDepth := by
    rw [← gatherRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have gatherCorrect : forall incidence,
      recordValue gatherOutput
          (Fin.castLE gatherDestinationFits incidence) =
        fun bit => decodeBinaryExtension widthPositive
          (packedEvaluationResource widthPositive placement function
            (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
              incidence).2
            (requestSuffix (incidenceAt incidence).1)) bit := by
    intro incidence
    exact gather_evaluatedPackedResources_routes_incidence widthPositive
      groupsPositive groupFits incidenceFits capacity scheduleOutput targets
      directions pointFormula withinGroupDisjoint placement function
      requestSuffix scatterDestinationSuffix scatterPaddingSuffix
      scatterRecordCount gateCounts resourceCircuits computes
      gatherDestinationValues gatherPaddingValues gatherRecordCount incidence
  have lineRecovers : forall request,
      (∑ scalar, decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function
          (requestScheduledLinePoint widthPositive capacity scheduleOutput
            request scalar)
          (requestSuffix request))
        (placement (requestSource request)).2) =
      function (requestSource request) (requestSuffix request) := by
    intro request
    let resource := fun point => decodeBinaryExtension widthPositive
      (packedEvaluationResource widthPositive placement function point
        (requestSuffix request))
      (placement (requestSource request)).2
    have pointInjective :=
      requestScheduledLinePoint_injective_of_formula widthPositive capacity
        scheduleOutput targets directions pointFormula request
    have sequenceToSet := sum_requestScheduledLinePoint_eq_set widthPositive
      capacity scheduleOutput resource request pointInjective
    have codeRecovery := packedEvaluationResource_sum_puncturedLine
      widthPositive dimensionPositive placement function
      (requestSource request) (requestSuffix request) (directions request)
    change (∑ scalar, resource
      (requestScheduledLinePoint widthPositive capacity scheduleOutput
        request scalar)) =
      function (requestSource request) (requestSuffix request)
    calc
      (∑ scalar, resource
          (requestScheduledLinePoint widthPositive capacity scheduleOutput
            request scalar)) =
          ∑ point ∈ requestScheduledLineSet widthPositive capacity
            scheduleOutput request, resource point := sequenceToSet
      _ = ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
            (packedTargetPoint widthPositive placement
              (requestSource request))
            (directions request), resource point := by
          rw [setFormula request]
      _ = function (requestSource request) (requestSuffix request) :=
        codeRecovery
  exact decoder_recovers_of_gatheredPackedResources widthPositive capacity
    scheduleOutput placement function requestSource requestSuffix gatherOutput
    gatherDestinationFits gatherCorrect lineRecovers

set_option maxHeartbeats 1500000 in
/-- The deterministic grouped greedy scheduler supplies all geometric
hypotheses of the finite end-to-end pipeline. -/
theorem grouped_scatter_evaluate_gather_decode_recovers
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterDestinationSuffix :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin suffixWidth -> Bool)
    (scatterPaddingSuffix : Fin scatterPaddingCount ->
      Fin suffixWidth -> Bool)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction widthPositive placement function point bit)
          groups))
    (gatherDestinationValues :
      Fin (totalRequests * nonzeroScalarCount width) -> Fin width -> Bool)
    (gatherPaddingValues : Fin gatherPaddingCount -> Fin width -> Bool)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    let targets : Fin totalRequests ->
        Fin dimension -> BinaryExtension width :=
      fun request => packedTargetPoint widthPositive placement
        (requestSource request)
    let groupSize := requestGroupSize totalRequests groups
    let capacity := requestGroupCapacity
      (totalRequests := totalRequests) groupsPositive
    let paddedTargets := paddedGroupedTargets capacity targets dummyTarget
    let scheduleOutput := groupedScheduleOutput dimension widthPositive
      schedulerDepth groups groupSize allFit paddedTargets
    let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
      capacity scheduleOutput requestSuffix scatterDestinationSuffix
      scatterPaddingSuffix scatterRecordCount
    let scatterDestinationFits :
        2 ^ (groupBitWidth + dimension * width) <=
          networkRecords scatterDepth := by
      rw [← scatterRecordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    let resourceValues := evaluatedResourceValues groupsPositive
      groupBitWidth dimension width scatterDepth suffixWidth
      scatterDestinationFits gateCounts resourceCircuits scatterOutput
    let gatherOutput := canonicalGatherBits widthPositive groupBitWidth
      orderWidth incidenceFits capacity scheduleOutput resourceValues
      gatherDestinationValues gatherPaddingValues gatherRecordCount
    let gatherDestinationFits :
        totalRequests * nonzeroScalarCount width <=
          networkRecords gatherDepth := by
      rw [← gatherRecordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    (GatherDecoder.circuit
        (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
        (metadataWidth := orderWidth + 1)
        gatherDestinationFits
        (fun request => (placement (requestSource request)).2)).eval
        DeMorgan.interpretation gatherOutput =
      fun request => function (requestSource request)
        (requestSuffix request) := by
  dsimp only
  let targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width :=
    fun request => packedTargetPoint widthPositive placement
      (requestSource request)
  let groupSize := requestGroupSize totalRequests groups
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  let paddedTargets := paddedGroupedTargets capacity targets dummyTarget
  let scheduleOutput := groupedScheduleOutput dimension widthPositive
    schedulerDepth groups groupSize allFit paddedTargets
  obtain ⟨directions, pointFormula, setFormula, withinGroupDisjoint⟩ :=
    paddedGroupedScheduleCircuit_correct widthPositive widthAtLeastTwo
      groupsPositive allFit directionCapacity targets dummyTarget
  exact scatter_evaluate_gather_decode_recovers widthPositive
    dimensionPositive groupsPositive groupFits incidenceFits capacity
    scheduleOutput placement function requestSource requestSuffix directions
    pointFormula setFormula withinGroupDisjoint scatterDestinationSuffix
    scatterPaddingSuffix scatterRecordCount gateCounts resourceCircuits
    computes gatherDestinationValues gatherPaddingValues gatherRecordCount

end PackedPipeline
end MassProduction
end Algebraic
