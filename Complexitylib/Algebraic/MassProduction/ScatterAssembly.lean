/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CanonicalScatter
public import Complexitylib.Algebraic.MassProduction.ScheduledRoutingWiring

/-!
# Scatter routing assembly

This module turns a grouped scheduler output and the corresponding request
suffixes into the fixed record layout consumed by canonical scatter routing.
The assembly layer consists only of constants and input wires; the subsequent
two-pass routing circuit performs the actual Boolean work.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RoutingAssembly

open CanonicalScatter
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open Sorting

/-! ## Scatter inputs -/

/-- Scheduler output followed by one suffix for every actual request. -/
@[reducible] noncomputable def scatterAssemblyInputCount
    (groups requestsPerGroup dimension width totalRequests suffixWidth : Nat) :
    Nat :=
  scheduleBitCount groups requestsPerGroup dimension width +
    totalRequests * suffixWidth

/-- Embed a scheduler-output wire into the scatter-assembly input. -/
noncomputable def scatterScheduleInputIndex
    (index : Fin (scheduleBitCount groups requestsPerGroup dimension width)) :
    Fin (scatterAssemblyInputCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.castAdd (totalRequests * suffixWidth) index

/-- Embed a row-major request-suffix wire into the scatter-assembly input. -/
noncomputable def scatterSuffixInputIndex
    (request : Fin totalRequests)
    (bit : Fin suffixWidth) :
    Fin (scatterAssemblyInputCount groups requestsPerGroup dimension width
      totalRequests suffixWidth) :=
  Fin.natAdd (scheduleBitCount groups requestsPerGroup dimension width)
    (finProdFinEquiv (request, bit))

/-- Scheduler-output view of the combined scatter-assembly input. -/
noncomputable def scatterScheduleInput
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    Fin (scheduleBitCount groups requestsPerGroup dimension width) -> Bool :=
  fun index => input (scatterScheduleInputIndex
    (totalRequests := totalRequests) (suffixWidth := suffixWidth) index)

/-- Request-suffix view of the combined scatter-assembly input. -/
noncomputable def scatterSuffixInput
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    Fin totalRequests -> Fin suffixWidth -> Bool :=
  fun request bit => input (scatterSuffixInputIndex
    (groups := groups) (requestsPerGroup := requestsPerGroup)
    (dimension := dimension) (width := width) request bit)

@[simp] theorem scatterScheduleInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool) :
    scatterScheduleInput (Fin.append schedule suffixes) = schedule := by
  funext index
  simp [scatterScheduleInput, scatterScheduleInputIndex]

@[simp] theorem scatterSuffixInput_append
    (schedule : Fin (scheduleBitCount groups requestsPerGroup dimension width) ->
      Bool)
    (suffixes : Fin (totalRequests * suffixWidth) -> Bool) :
    scatterSuffixInput (Fin.append schedule suffixes) =
      fun request bit => suffixes (finProdFinEquiv (request, bit)) := by
  funext request bit
  simp [scatterSuffixInput, scatterSuffixInputIndex]

/-! ## Zero-cost record assembly -/

/-- A scheduled incidence key consists only of constants and direct scheduler
output wires. -/
noncomputable def scatterSourceKeyWiring
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) ->
      DeMorgan.Wiring (scatterAssemblyInputCount groups requestsPerGroup dimension
        width totalRequests suffixWidth) :=
  let requestAndScalar := incidenceAt incidence
  let group := (requestGroupSlot capacity requestAndScalar.1).1
  Fin.cons (.constant false)
    (Fin.append
      (fun groupBit => .constant (finiteIndexBits groupBitWidth group groupBit))
      (fun pointBit => .input (scatterScheduleInputIndex
        (totalRequests := totalRequests) (suffixWidth := suffixWidth)
        (scheduledIncidencePointBitIndex capacity incidence pointBit))))

theorem scatterSourceKeyWiring_eval
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    (fun bit => (scatterSourceKeyWiring
      (suffixWidth := suffixWidth) groupBitWidth capacity incidence bit).eval
        input) =
      scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        (scatterScheduleInput input) incidence := by
  rw [scheduledIncidenceKeyBits_eq_wiring]
  funext bit
  refine Fin.cases ?_ (fun tailBit => ?_) bit
  · simp [scatterSourceKeyWiring, activeRoutingKey]
  · refine Fin.addCases (fun groupBit => ?_) (fun pointBit => ?_) tailBit
    · simp [scatterSourceKeyWiring, activeRoutingKey,
        scheduledIncidenceSlotAt, scheduledIncidenceSlot]
    · simp [scatterSourceKeyWiring, activeRoutingKey,
        scatterScheduleInput, scatterScheduleInputIndex]

/-- One source payload is a direct copy of its request's suffix wires. -/
noncomputable def scatterSourcePayloadWiring
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin suffixWidth ->
      DeMorgan.Wiring (scatterAssemblyInputCount groups requestsPerGroup dimension
        width totalRequests suffixWidth) :=
  fun bit => .input (scatterSuffixInputIndex
    (groups := groups) (requestsPerGroup := requestsPerGroup)
    (dimension := dimension) (width := width)
    (incidenceAt incidence).1 bit)

theorem scatterSourcePayloadWiring_eval
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    (fun bit => (scatterSourcePayloadWiring
      (groups := groups) (requestsPerGroup := requestsPerGroup)
      (dimension := dimension) (width := width) incidence bit).eval input) =
      incidenceSourcePayload (scatterSuffixInput input) incidence := by
  rfl

/-- Zero-gate wiring description of the complete scatter sorter input.
Destination and padding payloads are initialized to zero because their prior
contents are semantically irrelevant. -/
noncomputable def scatterAssemblySpecification
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :
    Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      DeMorgan.Wiring (scatterAssemblyInputCount groups requestsPerGroup dimension
        width totalRequests suffixWidth) :=
  wiringRoutingInputBits
    (scatterSourceKeyWiring (suffixWidth := suffixWidth)
      groupBitWidth capacity)
    (scatterSourcePayloadWiring (groups := groups)
      (requestsPerGroup := requestsPerGroup) (dimension := dimension)
      (width := width))
    (fun destination bit => .constant
      (fullResourceDestinationKeyBits groupBitWidth dimension width
        destination bit))
    (fun _destination _bit => .constant false)
    (fun _padding bit => .constant
      (incidencePaddingKey groupBitWidth dimension width bit))
    (fun _padding _bit => .constant false)
    recordCount

/-- Scatter record assembly itself uses no Boolean gates. -/
noncomputable def scatterAssemblyCircuit
    (suffixWidth : Nat)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :=
  DeMorgan.Wiring.circuit (scatterAssemblySpecification
    (suffixWidth := suffixWidth) groupBitWidth capacity recordCount)

@[simp] theorem scatterAssemblyCircuit_cost
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :
    (scatterAssemblyCircuit (suffixWidth := suffixWidth) groupBitWidth
      capacity recordCount).cost DeMorgan.standardCost = 0 := by
  exact DeMorgan.Wiring.circuit_cost _

theorem scatterAssemblyCircuit_eval
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    (scatterAssemblyCircuit (suffixWidth := suffixWidth) groupBitWidth
      capacity recordCount).eval DeMorgan.interpretation input =
      fullScatterRoutingInputBits widthPositive groupBitWidth capacity
        (scatterScheduleInput input) (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) recordCount := by
  rw [scatterAssemblyCircuit, DeMorgan.Wiring.circuit_eval,
    scatterAssemblySpecification, wiringRoutingInputBits_eval]
  unfold fullScatterRoutingInputBits
  congr 1
  · funext incidence
    exact scatterSourceKeyWiring_eval widthPositive groupBitWidth capacity
      input incidence

/-! ## Routed scatter -/

/-- Complete scatter routing, including its zero-cost record assembly. -/
noncomputable def scatterRoutingCircuit
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :=
  (CanonicalRouting.matchedCanonicalRoutingCircuit routingDepth
    (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).comp
      (scatterAssemblyCircuit suffixWidth groupBitWidth capacity recordCount)

@[simp] theorem scatterRoutingCircuit_cost
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :
    (scatterRoutingCircuit suffixWidth groupBitWidth capacity recordCount).cost
        DeMorgan.standardCost =
      (CanonicalRouting.matchedCanonicalRoutingCircuit routingDepth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth).cost
          DeMorgan.standardCost := by
  rw [scatterRoutingCircuit, Circuit.cost_comp,
    scatterAssemblyCircuit_cost, Nat.zero_add]

theorem scatterRoutingCircuit_eval
    (widthPositive : 0 < width)
    (suffixWidth groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth)
    (input : Fin (scatterAssemblyInputCount groups requestsPerGroup
      dimension width totalRequests suffixWidth) -> Bool) :
    (scatterRoutingCircuit suffixWidth groupBitWidth capacity recordCount).eval
        DeMorgan.interpretation input =
      canonicalFullScatterBits widthPositive groupBitWidth capacity
        (scatterScheduleInput input) (scatterSuffixInput input)
        (fun _destination _bit => false)
        (fun _padding _bit => false) recordCount := by
  rw [scatterRoutingCircuit, Circuit.eval_comp,
    CanonicalRouting.matchedCanonicalRoutingCircuit_eval,
    scatterAssemblyCircuit_eval widthPositive]
  rfl

end RoutingAssembly
end MassProduction
end Algebraic
