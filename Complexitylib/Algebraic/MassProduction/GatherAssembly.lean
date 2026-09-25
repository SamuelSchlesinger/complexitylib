/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.ResourceEvaluation
public import Complexitylib.Algebraic.MassProduction.ScheduledRoutingWiring

/-!
# Gather routing assembly

This module turns a grouped scheduler output and a complete resource bank
into the fixed metadata-bearing record layout consumed by canonical gather
routing. Record assembly is zero-cost wiring; the routing network returns
resource values to incidence order.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RoutingAssembly

open CanonicalMetadataRouting
open GatherRouting
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open ResourceEvaluation
open Sorting

/-! ## Gather inputs -/

/-- Scheduler output followed by the complete resource-bank output. -/
@[reducible] noncomputable def gatherAssemblyInputCount
    (groups requestsPerGroup dimension width : Nat) : Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    resourceBitCount dimension width * groups

/-- Embed one scheduler bit in the gather-assembly input. -/
noncomputable def gatherScheduleInputIndex
    (index : Fin (scheduleBitCount groups requestsPerGroup dimension width)) :
    Fin (gatherAssemblyInputCount groups requestsPerGroup dimension width) :=
  Fin.castAdd (resourceBitCount dimension width * groups) index

/-- Embed one resource-bank output bit in the gather-assembly input. -/
noncomputable def gatherBankInputIndex
    (index : Fin (resourceBitCount dimension width * groups)) :
    Fin (gatherAssemblyInputCount groups requestsPerGroup dimension width) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width) index

/-- Scheduler view of a gather-assembly input. -/
noncomputable def gatherScheduleInput
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool :=
  fun index => input (gatherScheduleInputIndex index)

/-- Resource-bank view of a gather-assembly input. -/
noncomputable def gatherBankInput
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    Fin (resourceBitCount dimension width * groups) -> Bool :=
  fun index => input (gatherBankInputIndex
    (requestsPerGroup := requestsPerGroup) index)

@[simp] theorem gatherScheduleInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (bank : Fin (resourceBitCount dimension width * groups) -> Bool) :
    gatherScheduleInput (Fin.append schedule bank) = schedule := by
  funext index
  simp [gatherScheduleInput, gatherScheduleInputIndex]

@[simp] theorem gatherBankInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (bank : Fin (resourceBitCount dimension width * groups) -> Bool) :
    gatherBankInput (Fin.append schedule bank) = bank := by
  funext index
  simp [gatherBankInput, gatherBankInputIndex]

/-! ## Zero-cost record assembly -/

/-- Every full resource-source key is a construction-time constant. -/
noncomputable def gatherSourceKeyWiring
    (groupBitWidth dimension width : Nat)
    (source : Fin (2 ^ (groupBitWidth + dimension * width))) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) ->
      DeMorgan.Wiring inputs :=
  fun bit => .constant
    (fullResourceDestinationKeyBits groupBitWidth dimension width source bit)

/-- The resource value attached to a full-key source is selected directly
from the corresponding resource-bank output.  Invalid group encodings use
the same fixed group-zero convention as `resourceValuesFromBank`. -/
noncomputable def gatherSourcePayloadWiring
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (source : Fin (2 ^ (groupBitWidth + dimension * width))) :
    Fin ((orderWidth + 1) + width) ->
      DeMorgan.Wiring (gatherAssemblyInputCount groups requestsPerGroup dimension
        width) :=
  Fin.append
    (fun _metadataBit => .constant false)
    (fun valueBit => .input (gatherBankInputIndex
      (requestsPerGroup := requestsPerGroup)
      (finProdFinEquiv
        (resourceMemberIndex
          (fullDestinationPointIndex groupBitWidth dimension width source)
          valueBit,
        decodedGroupOrZero groupsPositive groupBitWidth
          (fullDestinationGroupBits groupBitWidth (dimension * width)
            source)))))

theorem gatherSourcePayloadWiring_eval
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool)
    (source : Fin (2 ^ (groupBitWidth + dimension * width))) :
    (fun bit => (gatherSourcePayloadWiring
      (requestsPerGroup := requestsPerGroup)
      groupsPositive groupBitWidth orderWidth source bit).eval input) =
      Fin.append (resourceSourceMetadata orderWidth source)
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          (gatherBankInput input) source) := by
  funext bit
  refine Fin.addCases (fun metadataBit => ?_) (fun valueBit => ?_) bit
  · simp [gatherSourcePayloadWiring, resourceSourceMetadata]
  · simp [gatherSourcePayloadWiring, resourceValuesFromBank,
      gatherBankInput, gatherBankInputIndex]

/-- A gather destination uses the same scheduled matching key as the
corresponding scatter source. -/
noncomputable def gatherDestinationKeyWiring
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) ->
      DeMorgan.Wiring (gatherAssemblyInputCount groups requestsPerGroup dimension
        width) :=
  let requestAndScalar := incidenceAt incidence
  let group := (requestGroupSlot capacity requestAndScalar.1).1
  Fin.cons (.constant false)
    (Fin.append
      (fun groupBit => .constant (finiteIndexBits groupBitWidth group groupBit))
      (fun pointBit => .input (gatherScheduleInputIndex
        (scheduledIncidencePointBitIndex capacity incidence pointBit))))

theorem gatherDestinationKeyWiring_eval
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    (fun bit => (gatherDestinationKeyWiring groupBitWidth capacity incidence
      bit).eval input) =
      scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        (gatherScheduleInput input) incidence := by
  rw [scheduledIncidenceKeyBits_eq_wiring]
  funext bit
  refine Fin.cases ?_ (fun tailBit => ?_) bit
  · simp [gatherDestinationKeyWiring, activeRoutingKey]
  · refine Fin.addCases (fun groupBit => ?_) (fun pointBit => ?_) tailBit
    · simp [gatherDestinationKeyWiring, activeRoutingKey,
        scheduledIncidenceSlotAt, scheduledIncidenceSlot]
    · simp [gatherDestinationKeyWiring, activeRoutingKey,
        gatherScheduleInput, gatherScheduleInputIndex]

/-- Destination ordering metadata is constant and its unused value field is
initialized to zero. -/
noncomputable def gatherDestinationPayloadWiring
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin ((orderWidth + 1) + width) -> DeMorgan.Wiring inputs :=
  Fin.append
    (fun metadataBit => .constant
      (destinationOrderMetadata incidenceFits incidence metadataBit))
    (fun _valueBit => .constant false)

/-- Gather padding uses a reserved metadata marker and a zero value. -/
noncomputable def gatherPaddingPayloadWiring
    (orderWidth width : Nat) :
    Fin ((orderWidth + 1) + width) -> DeMorgan.Wiring inputs :=
  Fin.append
    (fun metadataBit => .constant
      (paddingRoutingKey (fun _ : Fin orderWidth => false) metadataBit))
    (fun _valueBit => .constant false)

theorem gatherDestinationPayloadWiring_eval
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (input : Fin inputs -> Bool) :
    (fun bit => (gatherDestinationPayloadWiring incidenceFits incidence bit).eval
      input) =
      Fin.append (destinationOrderMetadata incidenceFits incidence)
        (fun _bit : Fin width => false) := by
  funext bit
  refine Fin.addCases (fun metadataBit => ?_) (fun valueBit => ?_) bit
  · simp [gatherDestinationPayloadWiring]
  · simp [gatherDestinationPayloadWiring]

theorem gatherPaddingPayloadWiring_eval
    (orderWidth width : Nat)
    (input : Fin inputs -> Bool) :
    (fun bit => (gatherPaddingPayloadWiring (inputs := inputs) orderWidth width
      bit).eval input) =
      Fin.append (paddingRoutingKey (fun _ : Fin orderWidth => false))
        (fun _bit : Fin width => false) := by
  funext bit
  refine Fin.addCases (fun metadataBit => ?_) (fun valueBit => ?_) bit
  · simp [gatherPaddingPayloadWiring]
  · simp [gatherPaddingPayloadWiring]

/-- Pure wiring specification for the gather-routing input array. -/
noncomputable def gatherAssemblySpecification
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :
    Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width)
        ((orderWidth + 1) + width))) ->
      DeMorgan.Wiring (gatherAssemblyInputCount groups requestsPerGroup dimension
        width) :=
  wiringRoutingInputBits
    (gatherSourceKeyWiring groupBitWidth dimension width)
    (gatherSourcePayloadWiring (requestsPerGroup := requestsPerGroup)
      groupsPositive groupBitWidth orderWidth)
    (gatherDestinationKeyWiring groupBitWidth capacity)
    (gatherDestinationPayloadWiring incidenceFits)
    (fun _padding bit => .constant
      (incidencePaddingKey groupBitWidth dimension width bit))
    (fun _padding => gatherPaddingPayloadWiring orderWidth width)
    recordCount

/-- Gather record assembly uses only wire selection and constants. -/
noncomputable def gatherAssemblyCircuit
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :=
  DeMorgan.Wiring.circuit (gatherAssemblySpecification groupsPositive
    groupBitWidth orderWidth incidenceFits capacity recordCount)

@[simp] theorem gatherAssemblyCircuit_cost
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :
    (gatherAssemblyCircuit groupsPositive groupBitWidth
      orderWidth incidenceFits capacity recordCount).cost
        DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

theorem gatherAssemblyCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    (gatherAssemblyCircuit groupsPositive groupBitWidth
      orderWidth incidenceFits capacity recordCount).eval
        DeMorgan.interpretation input =
      Routing.routingInputBits
        (fullResourceDestinationKeyBits groupBitWidth dimension width)
        (fun source => Fin.append (resourceSourceMetadata orderWidth source)
          (resourceValuesFromBank groupsPositive groupBitWidth dimension width
            (gatherBankInput input) source))
        (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
          (gatherScheduleInput input))
        (fun destination => Fin.append
          (destinationOrderMetadata incidenceFits destination)
          (fun _bit : Fin width => false))
        (fun _padding => incidencePaddingKey groupBitWidth dimension width)
        (fun _padding => Fin.append
          (paddingRoutingKey (fun _ : Fin orderWidth => false))
          (fun _bit : Fin width => false))
        recordCount := by
  rw [gatherAssemblyCircuit, DeMorgan.Wiring.circuit_eval,
    gatherAssemblySpecification, wiringRoutingInputBits_eval]
  congr 1
  · funext source
    exact gatherSourcePayloadWiring_eval groupsPositive groupBitWidth
      orderWidth input source
  · funext incidence
    exact gatherDestinationKeyWiring_eval widthPositive groupBitWidth
      capacity input incidence
  · funext destination
    exact gatherDestinationPayloadWiring_eval incidenceFits destination input
  · funext padding
    exact gatherPaddingPayloadWiring_eval orderWidth width input

/-! ## Routed gather -/

/-- Complete metadata-preserving gather routing, including zero-cost record
assembly. -/
noncomputable def gatherRoutingCircuit
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :=
  (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit routingDepth
    (incidenceKeyWidth groupBitWidth dimension width)
    (orderWidth + 1) width).comp
      (gatherAssemblyCircuit groupsPositive groupBitWidth orderWidth
        incidenceFits capacity recordCount)

@[simp] theorem gatherRoutingCircuit_cost
    (groupsPositive : 0 < groups)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :
    (gatherRoutingCircuit groupsPositive groupBitWidth orderWidth
      incidenceFits capacity recordCount).cost DeMorgan.standardCost =
      (CanonicalMetadataRouting.matchedCanonicalRoutingCircuit routingDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) width).cost DeMorgan.standardCost := by
  rw [gatherRoutingCircuit, Circuit.cost_comp,
    gatherAssemblyCircuit_cost, Nat.zero_add]

theorem gatherRoutingCircuit_eval
    (groupsPositive : 0 < groups)
    (widthPositive : 0 < width)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth)
    (input : Fin (gatherAssemblyInputCount groups requestsPerGroup dimension
      width) -> Bool) :
    (gatherRoutingCircuit groupsPositive groupBitWidth orderWidth
      incidenceFits capacity recordCount).eval DeMorgan.interpretation input =
      canonicalGatherBits widthPositive groupBitWidth orderWidth incidenceFits
        capacity (gatherScheduleInput input)
        (resourceValuesFromBank groupsPositive groupBitWidth dimension width
          (gatherBankInput input))
        (fun _destination _bit => false)
        (fun _padding _bit => false) recordCount := by
  rw [gatherRoutingCircuit, Circuit.eval_comp,
    CanonicalMetadataRouting.matchedCanonicalRoutingCircuit_eval,
    gatherAssemblyCircuit_eval groupsPositive widthPositive]
  rfl

end RoutingAssembly
end MassProduction
end Algebraic
