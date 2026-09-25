/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CanonicalRouting

/-!
# Fixed-wire incidence scatter

This module closes the positional gap in the concrete scatter pass.  The
first verified sort routes each request suffix to its unique `(group, point)`
destination.  The second verified sort places the complete active resource
key space in canonical lexicographic order.  Consequently each incidence's
payload appears on the literal, input-independent wire indexed by its encoded
resource slot.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace CanonicalScatter

open scoped LinearAlgebra.Projectivization
open CanonicalRouting
open GroupedRecovery
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open SchedulerIteration
open Sorting

/-- Full scatter followed by canonical destination ordering. -/
noncomputable def canonicalFullScatterBits
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (requestPayload : Fin totalRequests -> Fin payloadWidth -> Bool)
    (destinationPayload :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin payloadWidth -> Bool)
    (paddingPayload : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth) :
    Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) payloadWidth)) ->
      Bool :=
  matchedCanonicalRoutingBits routingDepth
    (incidenceKeyWidth groupBitWidth dimension width) payloadWidth
    (fullScatterRoutingInputBits widthPositive groupBitWidth capacity
      scheduleOutput requestPayload destinationPayload paddingPayload
      recordCount)

/-- Every scheduled incidence lands at its fixed full-key-space destination
wire with exactly its request payload. -/
theorem canonicalFullScatterBits_routes_incidence
    (widthPositive : 0 < width)
    (groupFits : groups <= 2 ^ groupBitWidth)
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
    (requestPayload : Fin totalRequests -> Fin payloadWidth -> Bool)
    (destinationPayload :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin payloadWidth -> Bool)
    (paddingPayload : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    let destination := fullIncidenceDestination widthPositive
      groupBitWidth capacity scheduleOutput incidence
    let destinationFits :
        2 ^ (groupBitWidth + dimension * width) <=
          networkRecords routingDepth := by omega
    Routing.recordPayload
        (canonicalFullScatterBits widthPositive groupBitWidth capacity
          scheduleOutput requestPayload destinationPayload paddingPayload
          recordCount)
        (Fin.castLE destinationFits destination) =
      requestPayload (incidenceAt incidence).1 := by
  dsimp only
  let baseWidth := groupBitWidth + dimension * width
  let input := fullScatterRoutingInputBits widthPositive groupBitWidth
    capacity scheduleOutput requestPayload destinationPayload paddingPayload
    recordCount
  let initiallySorted := bitonicSortBits
    (Routing.keyAndTagFitsRecord
      (incidenceKeyWidth groupBitWidth dimension width) payloadWidth)
    routingDepth true input
  let routed := Routing.predecessorCopyBits routingDepth
    (incidenceKeyWidth groupBitWidth dimension width) payloadWidth false true
    initiallySorted
  let complemented := complementRoutingTagsBits routingDepth
    (incidenceKeyWidth groupBitWidth dimension width) payloadWidth routed
  let output := canonicalFullScatterBits widthPositive groupBitWidth capacity
    scheduleOutput requestPayload destinationPayload paddingPayload recordCount
  let destination := fullIncidenceDestination widthPositive groupBitWidth
    capacity scheduleOutput incidence
  have destinationFits : 2 ^ baseWidth <= networkRecords routingDepth := by
    dsimp [baseWidth]
    omega
  let fixedIndex : Fin (networkRecords routingDepth) :=
    Fin.castLE destinationFits destination
  have routedWitness := fullScatterRoutingInputBits_routes_incidence
    widthPositive groupFits capacity scheduleOutput targets directions
    pointFormula withinGroupDisjoint requestPayload destinationPayload
    paddingPayload recordCount incidence
  dsimp only at routedWitness
  obtain ⟨routedIndex, sortedIndexMatches, routedPayload⟩ := routedWitness
  rw [Routing.sortedPredecessorCopyCircuit_eval] at routedPayload
  change Routing.recordPayload routed routedIndex =
    requestPayload (incidenceAt incidence).1 at routedPayload
  have destinationKeyEquality :
      activeRoutingKey (lexBitVectorAt destination) =
        scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
          scheduleOutput incidence := by
    simpa [fullResourceDestinationKeyBits] using
      (fullResourceDestinationKeyBits_fullIncidenceDestination
        (totalRequests := totalRequests) (groups := groups)
        (requestsPerGroup := requestsPerGroup) (dimension := dimension)
        (width := width) widthPositive groupBitWidth capacity scheduleOutput
        incidence)
  have fixedHeader :
      recordHeader (flatRecords output fixedIndex) =
        activeDestinationHeader (lexBitVectorAt destination) := by
    let genericInput := Routing.routingInputBits
      (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        scheduleOutput)
      (incidenceSourcePayload requestPayload)
      (fun destination => activeRoutingKey (lexBitVectorAt destination))
      destinationPayload
      (fun _padding : Fin paddingCount =>
        paddingRoutingKey (fun _ : Fin baseWidth => false))
      paddingPayload recordCount
    have generic := matchedCanonicalRoutingBits_fullDest_fixed_header
      (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        scheduleOutput)
      (incidenceSourcePayload requestPayload)
      destinationPayload
      (fun _padding : Fin paddingCount => fun _ : Fin baseWidth => false)
      paddingPayload recordCount destination
    dsimp only at generic
    have inputEquality : input = genericInput := by
      rfl
    have outputEquality : output =
        matchedCanonicalRoutingBits routingDepth (baseWidth + 1)
          payloadWidth genericInput := by
      change matchedCanonicalRoutingBits routingDepth
          (incidenceKeyWidth groupBitWidth dimension width) payloadWidth
          input =
        matchedCanonicalRoutingBits routingDepth (baseWidth + 1)
          payloadWidth genericInput
      rw [inputEquality]
    rw [outputEquality]
    convert generic using 1
  have destinationKeyInjective : Function.Injective
      (fullResourceDestinationKeyBits groupBitWidth dimension width) :=
    fullResourceDestinationKeyBits_injective
  have paddingAvoids : forall (_padding : Fin paddingCount)
      (destinationIndex : Fin (2 ^ baseWidth)),
      incidencePaddingKey groupBitWidth dimension width ≠
        fullResourceDestinationKeyBits groupBitWidth dimension width
          destinationIndex := by
    intro _padding destinationIndex
    exact incidencePaddingKey_avoids (lexBitVectorAt destinationIndex)
  have uniqueInitial := Routing.routingInputBits_unique_destination
    (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
      scheduleOutput)
    (incidenceSourcePayload requestPayload)
    (fullResourceDestinationKeyBits groupBitWidth dimension width)
    destinationPayload
    (fun _ => incidencePaddingKey groupBitWidth dimension width)
    paddingPayload destinationKeyInjective paddingAvoids recordCount
    destination
  have uniqueInitialAtInput :
      Sorting.Semantics.UniqueIndexWhere (flatRecords input)
      (Routing.recordHasKeyTag
        (activeRoutingKey (lexBitVectorAt destination)) true) := by
    simpa [input, fullScatterRoutingInputBits,
      fullResourceDestinationKeyBits] using uniqueInitial
  have initiallySortedPermutes : FlatRecordsPermute initiallySorted input := by
    exact bitonicSortBits_recordsPermute
      (Routing.keyAndTagFitsRecord
        (incidenceKeyWidth groupBitWidth dimension width) payloadWidth)
      routingDepth true input
  have uniqueInitiallySorted :=
    Sorting.FlatRecordsPermute.uniqueIndexWhere initiallySortedPermutes
      uniqueInitialAtInput
  obtain ⟨uniqueIndex, uniqueIndexMatches, uniqueIndexOnly⟩ :=
    uniqueInitiallySorted
  have routedIndexMatches : Routing.recordHasKeyTag
      (activeRoutingKey (lexBitVectorAt destination)) true
      (flatRecords initiallySorted routedIndex) := by
    rw [destinationKeyEquality]
    exact sortedIndexMatches
  have routedIndexEquality : routedIndex = uniqueIndex :=
    uniqueIndexOnly routedIndex routedIndexMatches
  have canonicalRecords : FlatRecordsPermute output complemented := by
    change FlatRecordsPermute
      (canonicalSortBits routingDepth
        (incidenceKeyWidth groupBitWidth dimension width) payloadWidth routed)
      complemented
    exact canonicalSortBits_recordsPermute routed
  obtain ⟨preCanonicalIndex, recordEquality⟩ :=
    Sorting.FlatRecordsPermute.rangeContained canonicalRecords fixedIndex
  have preCanonicalHeader :
      recordHeader (flatRecords complemented preCanonicalIndex) =
        activeDestinationHeader (lexBitVectorAt destination) := by
    rw [← recordEquality]
    exact fixedHeader
  have preCanonicalRoutedMatch : Routing.recordHasKeyTag
      (activeRoutingKey (lexBitVectorAt destination)) true
      (flatRecords routed preCanonicalIndex) := by
    exact (recordHeader_complement_eq_activeDestinationHeader_iff
      routed preCanonicalIndex (lexBitVectorAt destination)).mp
        preCanonicalHeader
  have preCanonicalSortedMatch : Routing.recordHasKeyTag
      (activeRoutingKey (lexBitVectorAt destination)) true
      (flatRecords initiallySorted preCanonicalIndex) := by
    exact (recordHasKeyTag_predecessorCopyBits_iff false true
      initiallySorted preCanonicalIndex
      (activeRoutingKey (lexBitVectorAt destination)) true).mp
        preCanonicalRoutedMatch
  have preCanonicalIndexEquality : preCanonicalIndex = routedIndex := by
    calc
      preCanonicalIndex = uniqueIndex :=
        uniqueIndexOnly preCanonicalIndex preCanonicalSortedMatch
      _ = routedIndex := routedIndexEquality.symm
  have payloadMoved := congrArg Routing.packedRecordPayload recordEquality
  simp only [Routing.packedRecordPayload_flatRecords] at payloadMoved
  calc
    Routing.recordPayload output fixedIndex =
        Routing.recordPayload complemented preCanonicalIndex := payloadMoved
    _ = Routing.recordPayload routed preCanonicalIndex :=
      complementRoutingTagsBits_recordPayload routed preCanonicalIndex
    _ = Routing.recordPayload routed routedIndex := by
      rw [preCanonicalIndexEquality]
    _ = requestPayload (incidenceAt incidence).1 := routedPayload

end CanonicalScatter
end MassProduction
end Algebraic
