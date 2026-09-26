/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CanonicalMetadataRouting

/-!
# Fixed-wire gather from evaluated resource slots

The gather source array contains one evaluated value for every canonical
`(group, point)` key.  Its destinations are the scheduled incidences, whose
preserved metadata is their row-major `(request, scalar)` index.  Matching
routes each resource value back to its incidence; the metadata sort then puts
incidence `i` on literal output record `i`.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace GatherRouting

open scoped LinearAlgebra.Projectivization
open CanonicalMetadataRouting
open GroupedRecovery
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open RoutingMetadata
open SchedulerIteration
open Sorting

/-- Metadata attached to resource-source records is semantically irrelevant:
source tags put them after every gather destination in the canonical pass. -/
def resourceSourceMetadata
    (orderWidth : Nat)
    (_source : Fin sourceCount) : Fin (orderWidth + 1) -> Bool :=
  fun _ => false

/-- Canonically metadata-ordered gather output. -/
noncomputable def canonicalGatherBits
    (widthPositive : 0 < width)
    (groupBitWidth orderWidth : Nat)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (resourceValues :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin valueWidth -> Bool)
    (destinationValues :
      Fin (totalRequests * nonzeroScalarCount width) ->
        Fin valueWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth) :
    Fin (networkBits routingDepth
      (recordWidth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) valueWidth)) -> Bool :=
  let input := Routing.routingInputBits
    (fullResourceDestinationKeyBits groupBitWidth dimension width)
    (fun source => Fin.append (resourceSourceMetadata orderWidth source)
      (resourceValues source))
    (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
      scheduleOutput)
    (fun destination => Fin.append
      (destinationOrderMetadata
        (destinationCount := totalRequests * nonzeroScalarCount width)
        (orderWidth := orderWidth)
        incidenceFits destination)
      (destinationValues destination))
    (fun _padding => incidencePaddingKey groupBitWidth dimension width)
    (fun padding => Fin.append
      (paddingRoutingKey (fun _ : Fin orderWidth => false))
      (paddingValues padding))
    recordCount
  matchedCanonicalRoutingBits routingDepth
    (incidenceKeyWidth groupBitWidth dimension width)
    (orderWidth + 1) valueWidth input

/-- The reusable two-sort value-routing circuit underlying gather.  Record
assembly is kept explicit at the composition boundary. -/
def canonicalGatherCircuit
    (routingDepth groupBitWidth dimension width orderWidth valueWidth : Nat) :=
  matchedCanonicalRoutingCircuit routingDepth
    (incidenceKeyWidth groupBitWidth dimension width)
    (orderWidth + 1) valueWidth

/-- `canonicalGatherCircuit` has exactly the gates of `matchedCanonicalRoutingCircuit`; the
surrounding wiring adds none. -/
@[simp] theorem canonicalGatherCircuit_size
    (routingDepth groupBitWidth dimension width orderWidth valueWidth : Nat) :
    (canonicalGatherCircuit routingDepth groupBitWidth dimension width orderWidth valueWidth).size =
      (matchedCanonicalRoutingCircuit routingDepth
          (incidenceKeyWidth groupBitWidth dimension width) (orderWidth + 1)
          valueWidth).size := by
  simp [canonicalGatherCircuit]

@[simp] theorem canonicalGatherCircuit_eval
    (input : Fin (networkBits routingDepth
      (recordWidth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) valueWidth)) -> Bool) :
    (canonicalGatherCircuit routingDepth groupBitWidth dimension width
      orderWidth valueWidth).eval DeMorgan.interpretation input =
      matchedCanonicalRoutingBits routingDepth
        (incidenceKeyWidth groupBitWidth dimension width)
        (orderWidth + 1) valueWidth input := by
  exact matchedCanonicalRoutingCircuit_eval input

theorem canonicalGatherCircuit_cost_le :
    (canonicalGatherCircuit routingDepth groupBitWidth dimension width
      orderWidth valueWidth).cost DeMorgan.standardCost <=
      (routingDepth * routingDepth * networkRecords routingDepth *
          ((2 * recordWidth
            (incidenceKeyWidth groupBitWidth dimension width)
            (orderWidth + 1) valueWidth) *
            (2 * ((incidenceKeyWidth groupBitWidth dimension width + 1) *
              (6 * (incidenceKeyWidth groupBitWidth dimension width + 1) +
                4)) + 4)) +
        networkBits routingDepth
            (recordWidth (incidenceKeyWidth groupBitWidth dimension width)
              (orderWidth + 1) valueWidth) *
          (12 * incidenceKeyWidth groupBitWidth dimension width + 12)) +
      (networkBits routingDepth
          (recordWidth (incidenceKeyWidth groupBitWidth dimension width)
            (orderWidth + 1) valueWidth) +
        routingDepth * routingDepth * networkRecords routingDepth *
          ((2 * recordWidth
            (incidenceKeyWidth groupBitWidth dimension width)
            (orderWidth + 1) valueWidth) *
            (2 * (((orderWidth + 1) + 1) *
              (6 * ((orderWidth + 1) + 1) + 4)) + 4))) := by
  exact matchedCanonicalRoutingCircuit_cost_le

/-- Every scheduled incidence receives the value of its evaluated resource
slot and lands at its row-major fixed output position. -/
theorem canonicalGatherBits_routes_incidence
    (widthPositive : 0 < width)
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
    (resourceValues :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin valueWidth -> Bool)
    (destinationValues :
      Fin (totalRequests * nonzeroScalarCount width) ->
        Fin valueWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (recordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + paddingCount =
        networkRecords routingDepth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    let destinationFitsNetwork :
        totalRequests * nonzeroScalarCount width <=
          networkRecords routingDepth := by
      rw [← recordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    recordValue
        (canonicalGatherBits widthPositive groupBitWidth orderWidth
          incidenceFits capacity scheduleOutput resourceValues destinationValues
          paddingValues recordCount)
        (Fin.castLE destinationFitsNetwork incidence) =
      resourceValues
        (fullIncidenceDestination widthPositive groupBitWidth capacity
          scheduleOutput incidence) := by
  dsimp only
  let sourceMetadata := resourceSourceMetadata
    (sourceCount := 2 ^ (groupBitWidth + dimension * width)) orderWidth
  have sourceInjective : Function.Injective
      (fullResourceDestinationKeyBits groupBitWidth dimension width) :=
    fullResourceDestinationKeyBits_injective
  have destinationInjective : Function.Injective
      (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        scheduleOutput) :=
    scheduledIncidenceKeyBits_injective widthPositive groupFits capacity
      scheduleOutput targets directions pointFormula withinGroupDisjoint
  have matchingKey : forall destination,
      fullResourceDestinationKeyBits groupBitWidth dimension width
          (fullIncidenceDestination widthPositive groupBitWidth capacity
            scheduleOutput destination) =
        scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
          scheduleOutput destination := by
    intro destination
    exact fullResourceDestinationKeyBits_fullIncidenceDestination
      widthPositive groupBitWidth capacity scheduleOutput destination
  have paddingAvoids : forall (_padding : Fin paddingCount) destination,
      incidencePaddingKey groupBitWidth dimension width ≠
        scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
          scheduleOutput destination := by
    intro _padding destination
    exact incidencePaddingKey_avoids
      (resourceSlotKeyBits widthPositive groupBitWidth
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          destination))
  exact matchedCanonicalRoutingBits_fixed_value incidenceFits
    (fullResourceDestinationKeyBits groupBitWidth dimension width)
    sourceMetadata resourceValues
    (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
      scheduleOutput)
    destinationValues
    (fun _padding => incidencePaddingKey groupBitWidth dimension width)
    (fun _padding => fun _ : Fin orderWidth => false)
    paddingValues sourceInjective destinationInjective
    (fullIncidenceDestination widthPositive groupBitWidth capacity
      scheduleOutput)
    matchingKey paddingAvoids recordCount incidence

end GatherRouting
end MassProduction
end Algebraic
