/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.DynamicGatherDecoder
public import Complexitylib.Algebraic.MassProduction.PipelineAssembly
public import Complexitylib.Algebraic.MassProduction.RuntimeScheduleAssembly

/-!
# Runtime-selected pipeline assembly

This module preserves the runtime one-hot selectors beside the scheduled
scatter input, runs scatter, resource evaluation, and gather, then performs
dynamic coordinate selection. It proves exact agreement with the established
fixed-selector pipeline and records the selector-decoding cost.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RuntimePipeline

universe u

variable {Prefix : Type u}

open DynamicGatherDecoder
open IncidenceRouting
open LineEnumeration
open ResourceEvaluation
open RoutingAssembly
open Sorting

/-! ## Dynamic scatter, evaluation, gather, and decoding -/

/-- Scheduler output, then row-major suffixes, then row-major selectors. -/
@[reducible] noncomputable def scheduledDataCount
    (groups requestsPerGroup dimension width totalRequests suffixWidth : Nat) :
    Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    suffixSelectorCount totalRequests suffixWidth width

/-- Embed the scheduler-and-suffix prefix consumed by scatter routing. -/
noncomputable def scheduledScatterInputIndex
    (index : Fin (scatterAssemblyInputCount groups requestsPerGroup dimension
      width totalRequests suffixWidth)) :
    Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.addCases
    (fun schedule => Fin.castAdd
      (suffixSelectorCount totalRequests suffixWidth width) schedule)
    (fun suffix => Fin.natAdd
      (scheduleBitCount groups requestsPerGroup dimension width)
      (Fin.castAdd (totalRequests * width) suffix))
    index

/-- Embed the final selector block. -/
noncomputable def scheduledSelectorInputIndex
    (selector : Fin (totalRequests * width)) :
    Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width)
    (Fin.natAdd (totalRequests * suffixWidth) selector)

/-- Scheduler-and-suffix view of scheduled runtime data. -/
noncomputable def scheduledScatterInput
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool) :
    Fin (scatterAssemblyInputCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool :=
  fun index => input (scheduledScatterInputIndex index)

/-- Selector view of scheduled runtime data. -/
noncomputable def scheduledSelectorInput
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool) :
    Fin (totalRequests * width) -> Bool :=
  fun selector => input (scheduledSelectorInputIndex selector)

@[simp] theorem scheduledScatterInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool)
    (selectors : Fin (totalRequests * width) -> Bool) :
    scheduledScatterInput
        (Fin.append schedule (Fin.append suffixes selectors)) =
      Fin.append schedule suffixes := by
  funext index
  refine Fin.addCases (fun scheduleIndex => ?_)
    (fun suffixIndex => ?_) index
  · simp [scheduledScatterInput, scheduledScatterInputIndex]
  · simp [scheduledScatterInput, scheduledScatterInputIndex]

@[simp] theorem scheduledSelectorInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool)
    (selectors : Fin (totalRequests * width) -> Bool) :
    scheduledSelectorInput
        (Fin.append schedule (Fin.append suffixes selectors)) =
      selectors := by
  funext selector
  simp [scheduledSelectorInput, scheduledSelectorInputIndex]

/-- Preserve runtime selectors alongside the gathered incidence records. -/
noncomputable def gatherWithSelectorsCircuit
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
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
  ((scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
    orderWidth incidenceFits capacity scatterRecordCount
    scatterDestinationFits resourceCircuits
    gatherRecordCount).mapInputs scheduledScatterInputIndex).parallel
    ((Circuit.id DeMorgan.signature
      (scheduledDataCount groups requestsPerGroup dimension width
        totalRequests suffixWidth)).mapOutputs
        scheduledSelectorInputIndex)

/-- Carrying the runtime selectors alongside the gathered records is pure wiring. -/
@[simp] theorem gatherWithSelectorsCircuit_size
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
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
    (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth orderWidth incidenceFits
      capacity scatterRecordCount resourceCircuits gatherRecordCount).size =
      (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount
        (by
          rw [← scatterRecordCount]
          exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
        resourceCircuits gatherRecordCount).size := by
  simp [gatherWithSelectorsCircuit]

theorem gatherWithSelectorsCircuit_eval
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
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
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool) :
    (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      resourceCircuits gatherRecordCount).eval DeMorgan.interpretation input =
      let scatterDestinationFits :
          2 ^ (groupBitWidth + dimension * width) <=
            networkRecords scatterDepth := by
        rw [← scatterRecordCount]
        exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
      Fin.append
        ((scatterResourceGatherCircuit groupsPositive suffixWidth
          groupBitWidth orderWidth incidenceFits capacity scatterRecordCount
          scatterDestinationFits resourceCircuits
          gatherRecordCount).eval DeMorgan.interpretation
            (scheduledScatterInput input))
        (scheduledSelectorInput input) := by
  rw [gatherWithSelectorsCircuit, Circuit.eval_parallel,
    Circuit.eval_mapInputs, Circuit.eval_mapOutputs, Circuit.eval_id]
  rfl

@[simp] theorem gatherWithSelectorsCircuit_cost
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
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
    (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      (scatterResourceGatherCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount (by
          rw [← scatterRecordCount]
          exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
         resourceCircuits gatherRecordCount).cost
          DeMorgan.standardCost := by
  simp [gatherWithSelectorsCircuit]

/-- Scatter, resource evaluation, gather, and runtime-selected decoding. -/
noncomputable def dynamicAssembledPipelineCircuit
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
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
  let gatherDestinationFits :
      totalRequests * nonzeroScalarCount width <=
        networkRecords gatherDepth := by
    rw [← gatherRecordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  (DynamicGatherDecoder.circuit
    (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
    (metadataWidth := orderWidth + 1)
    (valueWidth := width) gatherDestinationFits).comp
      (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount
        resourceCircuits gatherRecordCount)

/-- The dynamic pipeline has exactly the gates of the gather stage followed by one runtime decoder
per request. -/
@[simp] theorem dynamicAssembledPipelineCircuit_size
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
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
    (dynamicAssembledPipelineCircuit groupsPositive suffixWidth groupBitWidth orderWidth
      incidenceFits capacity scatterRecordCount resourceCircuits gatherRecordCount).size =
      (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth orderWidth
            incidenceFits capacity scatterRecordCount resourceCircuits
            gatherRecordCount).size +
        ∑ request : Fin totalRequests,
          decoderGateCount (width := width) (depth := gatherDepth)
            (incidenceKeyWidth groupBitWidth dimension width) (orderWidth + 1) width
            (by
              rw [← gatherRecordCount]
              exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _))
            request := by
  simp [dynamicAssembledPipelineCircuit]

set_option maxHeartbeats 1500000 in
/-- When the appended selectors are one-hot at the specified coordinates,
the dynamic pipeline is exactly the established fixed-selector pipeline. -/
theorem dynamicAssembledPipelineCircuit_eq_fixed
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
        networkRecords gatherDepth)
    (input : Fin (scheduledDataCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) -> Bool)
    (selectorCorrect : forall request bit,
      scheduledSelectorInput input (finProdFinEquiv (request, bit)) =
        decide (bit = (placement (requestSource request)).2)) :
    (dynamicAssembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      resourceCircuits gatherRecordCount).eval DeMorgan.interpretation input =
      (assembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity placement requestSource
        scatterRecordCount resourceCircuits
        gatherRecordCount).eval DeMorgan.interpretation
          (scheduledScatterInput input) := by
  let selectedBit : Fin totalRequests -> Fin width :=
    fun request => (placement (requestSource request)).2
  have selectorsEqual :
      scheduledSelectorInput input =
        fun flat =>
          let requestAndBit := (finProdFinEquiv
            (m := totalRequests) (n := width)).symm flat
          decide (requestAndBit.2 = selectedBit requestAndBit.1) := by
    funext flat
    obtain ⟨⟨request, bit⟩, rfl⟩ :=
      (finProdFinEquiv
        (m := totalRequests) (n := width)).surjective flat
    simpa [selectedBit] using selectorCorrect request bit
  rw [dynamicAssembledPipelineCircuit, Circuit.eval_comp,
    gatherWithSelectorsCircuit_eval]
  dsimp only
  rw [selectorsEqual,
    DynamicGatherDecoder.circuit_eval_append_oneHot]
  rw [assembledPipelineCircuit, Circuit.eval_comp]

@[simp] theorem dynamicAssembledPipelineCircuit_cost
    (groupsPositive : 0 < groups)
    (suffixWidth groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
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
    (dynamicAssembledPipelineCircuit groupsPositive suffixWidth groupBitWidth
      orderWidth incidenceFits capacity scatterRecordCount
      resourceCircuits gatherRecordCount).cost DeMorgan.standardCost =
      (gatherWithSelectorsCircuit groupsPositive suffixWidth groupBitWidth
        orderWidth incidenceFits capacity scatterRecordCount
        resourceCircuits gatherRecordCount).cost DeMorgan.standardCost +
      totalRequests * (nonzeroScalarCount width * width * 5) := by
  rw [dynamicAssembledPipelineCircuit, Circuit.cost_comp,
    DynamicGatherDecoder.circuit_cost]

end RuntimePipeline
end MassProduction
end Algebraic
