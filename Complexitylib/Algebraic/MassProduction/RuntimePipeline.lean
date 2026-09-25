/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.DynamicPipelineAssembly
public import Complexitylib.Algebraic.MassProduction.FiniteMassProductionCircuit
public import Complexitylib.Algebraic.MassProduction.RuntimeRequestData
public import Complexitylib.Algebraic.MassProduction.RuntimeScheduleAssembly

/-!
# Runtime-prefix mass-production pipeline

Building on the focused request, scheduling, and dynamic-pipeline layers, this
module replaces the hardwired-prefix front end of `RoutingAssembly`. Every
request supplies its prefix and suffix at runtime. The prefix determines both
its tensor-code target point and a one-hot basis-coordinate selector; the
suffix is passed unchanged to the routed resource bank.

All reindexing and padding layers are explicit zero-gate wiring circuits.  No
type-class instances are introduced.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RuntimePipeline

universe u

variable {Prefix : Type u}

open scoped LinearAlgebra.Projectivization
open CanonicalPacking
open DynamicGatherDecoder
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open ResourceEvaluation
open RoutingAssembly
open RuntimePacking
open SchedulerIteration
open Sorting

/-! ## Complete runtime-prefix assembly -/

/-- Row-major suffix array of the original runtime request input. -/
def runtimeSuffixArray
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    Fin (totalRequests * suffixWidth) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := suffixWidth)).symm flat
    requestSuffix input requestAndBit.1 requestAndBit.2

/-- Row-major one-hot selectors determined by all runtime prefixes. -/
noncomputable def runtimeSelectorArray
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    Fin (totalRequests * width) -> Bool :=
  fun flat =>
    let requestAndBit := (finProdFinEquiv
      (m := totalRequests) (n := width)).symm flat
    decide (requestAndBit.2 =
      requestSelectedBit packingFits input requestAndBit.1)

theorem processedSuffixArray_requestDataArray
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    processedSuffixArray
        ((requestDataArrayCircuit totalRequests prefixWidth dimension
          suffixWidth widthPositive gridPositive).eval
            DeMorgan.interpretation input) =
      runtimeSuffixArray input := by
  funext flat
  obtain ⟨⟨request, bit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := totalRequests) (n := suffixWidth)).surjective flat
  rw [processedSuffixArray, runtimeSuffixArray]
  simp only [Equiv.symm_apply_apply]
  exact requestDataArrayCircuit_eval_suffix widthPositive gridPositive
    input request bit

theorem processedSelectorArray_requestDataArray
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    processedSelectorArray
        ((requestDataArrayCircuit totalRequests prefixWidth dimension
          suffixWidth widthPositive gridPositive).eval
            DeMorgan.interpretation input) =
      runtimeSelectorArray packingFits input := by
  funext flat
  obtain ⟨⟨request, bit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := totalRequests) (n := width)).surjective flat
  rw [processedSelectorArray, runtimeSelectorArray]
  simp only [Equiv.symm_apply_apply]
  exact requestDataArrayCircuit_eval_selector widthPositive gridPositive
    packingFits input request bit

/-- Runtime packing for every request, followed by deterministic grouped
scheduling and retention of every suffix and selector bit. -/
noncomputable def runtimeScheduleSuffixSelectorCircuit
    (totalRequests groups prefixWidth dimension width suffixWidth
      schedulerDepth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :=
  let groupSize := requestGroupSize totalRequests groups
  (scheduleSuffixSelectorCircuit totalRequests groups groupSize dimension width
    suffixWidth schedulerDepth widthPositive allFit dummyTarget).comp
      (requestDataArrayCircuit totalRequests prefixWidth dimension suffixWidth
        widthPositive gridPositive)

theorem runtimeScheduleSuffixSelectorCircuit_eval
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    (runtimeScheduleSuffixSelectorCircuit totalRequests groups prefixWidth
      dimension width suffixWidth schedulerDepth widthPositive gridPositive
      allFit dummyTarget).eval DeMorgan.interpretation input =
      let groupSize := requestGroupSize totalRequests groups
      let capacity := requestGroupCapacity
        (totalRequests := totalRequests) groupsPositive
      let paddedTargets := paddedGroupedTargets capacity
        (requestTarget widthPositive packingFits input) dummyTarget
      Fin.append
        (groupedScheduleOutput dimension widthPositive schedulerDepth groups
          groupSize allFit paddedTargets)
        (Fin.append (runtimeSuffixArray input)
          (runtimeSelectorArray packingFits input)) := by
  rw [runtimeScheduleSuffixSelectorCircuit, Circuit.eval_comp]
  rw [scheduleSuffixSelectorCircuit_eval widthPositive allFit
    (requestGroupCapacity (totalRequests := totalRequests) groupsPositive)
    dummyTarget (requestTarget widthPositive packingFits input)
    _ (requestDataArrayCircuit_eval_target widthPositive gridPositive
      packingFits input)]
  rw [processedSuffixArray_requestDataArray,
    processedSelectorArray_requestDataArray]

@[simp] theorem runtimeScheduleSuffixSelectorCircuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= networkRecords schedulerDepth)
    (dummyTarget : Fin dimension -> BinaryExtension width) :
    (runtimeScheduleSuffixSelectorCircuit totalRequests groups prefixWidth
      dimension width suffixWidth schedulerDepth widthPositive gridPositive
      allFit dummyTarget).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost +
      totalRequests *
        (RuntimePacking.circuit prefixWidth dimension widthPositive
          gridPositive).cost DeMorgan.standardCost := by
  rw [runtimeScheduleSuffixSelectorCircuit, Circuit.cost_comp,
    scheduleSuffixSelectorCircuit_cost, requestDataArrayCircuit_cost]
  omega

/-- The complete exact mass-production circuit with runtime prefix and suffix
bits for every request. -/
def requestFunction
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool) :
    ScalarFunction Bool (requestInputCount prefixWidth suffixWidth) :=
  fun input =>
    function
      (RuntimePacking.source fun bit =>
        input (requestPrefixInputIndex prefixWidth suffixWidth bit))
      (fun bit =>
        input (requestSuffixInputIndex prefixWidth suffixWidth bit))

theorem directProduct_requestFunction_apply
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool)
    (request : Fin totalRequests) :
    directProduct (requestFunction function) totalRequests input request =
      function (requestSource input request) (requestSuffix input request) :=
  rfl

/-- Complete runtime mass-production circuit: schedule, scatter, evaluate,
gather, and decode every requested output. -/
noncomputable def circuit
    (prefixWidth : Nat)
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :=
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  (dynamicAssembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
    orderWidth incidenceFits capacity scatterRecordCount gateCounts
    resourceCircuits gatherRecordCount).comp
      (runtimeScheduleSuffixSelectorCircuit totalRequests groups prefixWidth
        dimension width suffixWidth schedulerDepth widthPositive gridPositive
        allFit dummyTarget)

set_option maxHeartbeats 2000000 in
/-- The complete runtime circuit returns every requested value in its original
request position.  In particular, the selected prefixes are runtime data,
not nonuniform parameters of the constructed circuit. -/
theorem circuit_recovers
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
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
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall
      (point : Fin (pointCount dimension width)) (bit : Fin width),
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction
            (Prefix := Fin (2 ^ prefixWidth))
            (dimension := dimension) (width := width)
            (suffixWidth := suffixWidth) widthPositive
            ((CanonicalPacking.packedPlacement widthPositive packingFits) :
              Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
            function point bit)
          groups))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth)
    (input : Fin (totalRequests *
      requestInputCount prefixWidth suffixWidth) -> Bool) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).eval DeMorgan.interpretation input =
      fun request => function (requestSource input request)
        (requestSuffix input request) := by
  let groupSize := requestGroupSize totalRequests groups
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  let placement :=
    CanonicalPacking.packedPlacement widthPositive packingFits
  let sources : Fin totalRequests -> Fin (2 ^ prefixWidth) :=
    requestSource input
  let schedule := groupedScheduleOutput dimension widthPositive
    schedulerDepth groups groupSize allFit
      (paddedGroupedTargets capacity
        (requestTarget widthPositive packingFits input) dummyTarget)
  let suffixes := runtimeSuffixArray input
  let selectors := runtimeSelectorArray packingFits input
  have selectorCorrect : forall request bit,
      scheduledSelectorInput
          (Fin.append schedule (Fin.append suffixes selectors))
          (finProdFinEquiv (request, bit)) =
        decide (bit = (placement (sources request)).2) := by
    intro request bit
    rw [scheduledSelectorInput_append]
    simp [selectors, runtimeSelectorArray, placement, sources,
      requestSelectedBit, requestSource]
  rw [circuit, Circuit.eval_comp,
    runtimeScheduleSuffixSelectorCircuit_eval widthPositive gridPositive
      groupsPositive packingFits]
  dsimp only
  rw [dynamicAssembledPipelineCircuit_eq_fixed
    (placement := placement) (requestSource := sources)
    (selectorCorrect := selectorCorrect)]
  rw [scheduledScatterInput_append]
  have targetsEqual :
      requestTarget widthPositive packingFits input =
        fun request => packedTargetPoint widthPositive placement
          (sources request) := by
    rfl
  have scheduleEqual : schedule =
      groupedScheduleOutput dimension widthPositive schedulerDepth groups
        groupSize allFit
        (paddedGroupedTargets capacity
          (fun request => packedTargetPoint widthPositive placement
            (sources request)) dummyTarget) := by
    dsimp [schedule]
    rw [targetsEqual]
  rw [scheduleEqual]
  have fixedRecovery := finiteMassProductionCircuit_recovers
    (totalRequests := totalRequests) (width := width)
    (dimension := dimension) (groups := groups)
    (schedulerDepth := schedulerDepth) (suffixWidth := suffixWidth)
    (groupBitWidth := groupBitWidth) (orderWidth := orderWidth)
    (scatterDepth := scatterDepth)
    (scatterPaddingCount := scatterPaddingCount)
    (gatherDepth := gatherDepth)
    (gatherPaddingCount := gatherPaddingCount)
    widthPositive widthAtLeastTwo dimensionPositive groupsPositive
    groupFits allFit directionCapacity incidenceFits placement function
    sources dummyTarget scatterRecordCount gateCounts resourceCircuits
    computes gatherRecordCount suffixes
  rw [finiteMassProductionCircuit_eval] at fixedRecovery
  simpa [groupSize, capacity, placement, sources, schedule, suffixes,
    requestTarget, runtimeSuffixArray] using fixedRecovery

set_option maxHeartbeats 2000000 in
/-- Public direct-product form of `circuit_recovers`: the constructed circuit
computes the standard row-major `totalRequests`-fold direct product. -/
theorem circuit_computes
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
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
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (computes : forall
      (point : Fin (pointCount dimension width)) (bit : Fin width),
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction
            (Prefix := Fin (2 ^ prefixWidth))
            (dimension := dimension) (width := width)
            (suffixWidth := suffixWidth) widthPositive
            ((CanonicalPacking.packedPlacement widthPositive packingFits) :
              Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
            function point bit)
          groups))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).ComputesWith DeMorgan.interpretation
        (directProduct (requestFunction function) totalRequests) := by
  intro input
  rw [circuit_recovers widthPositive widthAtLeastTwo dimensionPositive
    gridPositive groupsPositive packingFits schedulerDepth suffixWidth
    groupBitWidth orderWidth groupFits allFit directionCapacity incidenceFits
    function dummyTarget scatterRecordCount gateCounts resourceCircuits
    computes gatherRecordCount input]
  funext request
  exact (directProduct_requestFunction_apply function input request).symm

@[simp] theorem circuit_cost
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      ((groupedScheduleCircuit dimension widthPositive schedulerDepth groups
          (requestGroupSize totalRequests groups) allFit).cost
            DeMorgan.standardCost +
        totalRequests *
          (RuntimePacking.circuit prefixWidth dimension widthPositive
            gridPositive).cost DeMorgan.standardCost) +
      ((gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
          orderWidth incidenceFits
          (requestGroupCapacity (totalRequests := totalRequests)
            groupsPositive)
          scatterRecordCount gateCounts resourceCircuits
          gatherRecordCount).cost DeMorgan.standardCost +
        totalRequests * (nonzeroScalarCount width * width * 5)) := by
  rw [circuit, Circuit.cost_comp,
    runtimeScheduleSuffixSelectorCircuit_cost,
    dynamicAssembledPipelineCircuit_cost]

/-- Fully expanded finite ledger.  All zero-cost wiring has disappeared;
the only terms are packing, scheduling, the shorter resource circuits, two
routing passes, and runtime decoding. -/
theorem circuit_cost_expanded
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (gateCounts : Fin (resourceBitCount dimension width) -> Nat)
    (resourceCircuits : forall member,
      Circuit DeMorgan.signature (groups * suffixWidth)
        (gateCounts member) groups)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (circuit (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth
      allFit incidenceFits dummyTarget scatterRecordCount gateCounts
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      (groupedScheduleCircuit dimension widthPositive schedulerDepth groups
        (requestGroupSize totalRequests groups) allFit).cost
          DeMorgan.standardCost +
      totalRequests *
        (RuntimePacking.circuit prefixWidth dimension widthPositive
          gridPositive).cost DeMorgan.standardCost +
      (CanonicalRouting.matchedCanonicalRoutingCircuit scatterDepth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost +
      (∑ member,
        (resourceCircuits member).cost DeMorgan.standardCost) +
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit gatherDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost +
      totalRequests * (nonzeroScalarCount width * width * 5) := by
  rw [circuit_cost, gatherWithSelectorsCircuit_cost,
    scatterResourceGatherCircuit_cost]
  omega

end RuntimePipeline
end MassProduction
end Algebraic
