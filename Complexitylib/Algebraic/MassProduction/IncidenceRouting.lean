/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BinaryEncoding
public import Complexitylib.Algebraic.MassProduction.GroupedRecovery
public import Complexitylib.Algebraic.MassProduction.RoutingRecords

/-!
# Incidence keys for concrete scatter routing

Each scheduled `(request, nonzero scalar)` pair is one incidence.  Its
routing key is `(group, affine point)`.  Within-group line disjointness and
within-line scalar injectivity imply that all incidence keys are distinct.
The same structured keys index the complete rectangular resource-slot array,
giving the exact source-to-destination map required by the verified routing
primitive.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace IncidenceRouting

open scoped LinearAlgebra.Projectivization
open GroupedRecovery
open GroupedScheduler
open LineEnumeration
open SchedulerIteration
open Sorting

/-- A resource slot is identified by its request group and affine-space
coordinate. -/
abbrev ResourceSlot (groups dimension width : Nat) :=
  Fin groups × (Fin dimension -> BinaryExtension width)

/-- Structured slot requested by one scheduled line incidence. -/
noncomputable def scheduledIncidenceSlot
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin totalRequests × Fin (nonzeroScalarCount width)) :
    ResourceSlot groups dimension width :=
  ((requestGroupSlot capacity incidence.1).1,
    requestScheduledLinePoint widthPositive capacity output
      incidence.1 incidence.2)

/-- Every scalar-indexed point belongs to its decoded request recovery set. -/
theorem requestScheduledLinePoint_mem_set
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (request : Fin totalRequests)
    (scalar : Fin (nonzeroScalarCount width)) :
    requestScheduledLinePoint widthPositive capacity output request scalar ∈
      requestScheduledLineSet widthPositive capacity output request := by
  classical
  unfold requestScheduledLinePoint requestScheduledLineSet
  unfold scheduledLineSet LineEnumeration.decodedLineOutputSet
  apply Finset.mem_image.mpr
  exact ⟨scalar, Finset.mem_univ _, rfl⟩

/-- The scheduled `(group, point)` incidence keys are injective. -/
theorem scheduledIncidenceSlot_injective
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : forall request scalar,
      requestScheduledLinePoint widthPositive capacity output
          request scalar =
        targets request + enumeratedNonzeroScalar scalar •
          normalizeBinaryExtensionVector (directions request).rep)
    (withinGroupDisjoint : forall left right,
      (requestGroupSlot capacity left).1 =
          (requestGroupSlot capacity right).1 ->
      left ≠ right ->
        Disjoint
          (requestScheduledLineSet widthPositive capacity output left)
          (requestScheduledLineSet widthPositive capacity output right)) :
    Function.Injective
      (scheduledIncidenceSlot widthPositive capacity output) := by
  intro left right equalSlot
  have sameGroup :
      (requestGroupSlot capacity left.1).1 =
        (requestGroupSlot capacity right.1).1 :=
    by
      have equality := congrArg
        (fun slot : ResourceSlot groups dimension width => slot.1) equalSlot
      simpa only [scheduledIncidenceSlot] using equality
  have samePoint :
      requestScheduledLinePoint widthPositive capacity output
          left.1 left.2 =
        requestScheduledLinePoint widthPositive capacity output
          right.1 right.2 :=
    by
      have equality := congrArg
        (fun slot : ResourceSlot groups dimension width => slot.2) equalSlot
      simpa only [scheduledIncidenceSlot] using equality
  by_cases sameRequest : left.1 = right.1
  · have sameScalar : left.2 = right.2 := by
      apply requestScheduledLinePoint_injective_of_formula widthPositive
        capacity output targets directions pointFormula left.1
      simpa only [sameRequest] using samePoint
    exact Prod.ext sameRequest sameScalar
  · have disjoint := withinGroupDisjoint left.1 right.1 sameGroup sameRequest
    have leftMember := requestScheduledLinePoint_mem_set widthPositive
      capacity output left.1 left.2
    have rightMember := requestScheduledLinePoint_mem_set widthPositive
      capacity output right.1 right.2
    have notRight := (Finset.disjoint_left.mp disjoint) leftMember
    exact False.elim (notRight (samePoint ▸ rightMember))

/-- A fixed finite enumeration of all resource slots.  The particular order
is irrelevant here; it reuses the existing `Finite` structure without
installing a `Fintype` instance. -/
noncomputable def resourceSlotEquiv
    (groups dimension width : Nat) :
    ResourceSlot groups dimension width ≃
      Fin (Nat.card (ResourceSlot groups dimension width)) :=
  Finite.equivFin (ResourceSlot groups dimension width)

/-- Structured resource slot at one canonical destination index. -/
noncomputable def resourceSlotAt
    (destination : Fin (Nat.card
      (ResourceSlot groups dimension width))) :
    ResourceSlot groups dimension width :=
  (resourceSlotEquiv groups dimension width).symm destination

/-- Destination index of a structured resource slot. -/
noncomputable def resourceSlotIndex
    (slot : ResourceSlot groups dimension width) :
    Fin (Nat.card (ResourceSlot groups dimension width)) :=
  resourceSlotEquiv groups dimension width slot

@[simp] theorem resourceSlotAt_index
    (slot : ResourceSlot groups dimension width) :
    resourceSlotAt (resourceSlotIndex slot) = slot := by
  exact (resourceSlotEquiv groups dimension width).symm_apply_apply slot

@[simp] theorem resourceSlotIndex_at
    (destination : Fin (Nat.card
      (ResourceSlot groups dimension width))) :
    resourceSlotIndex (resourceSlotAt destination) = destination := by
  exact (resourceSlotEquiv groups dimension width).apply_symm_apply destination

/-- Flat row-major incidence index decoded as `(request, scalar)`. -/
noncomputable def incidenceAt
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin totalRequests × Fin (nonzeroScalarCount width) :=
  finProdFinEquiv.symm incidence

@[simp] theorem incidenceAt_finProdFinEquiv
    (request : Fin totalRequests)
    (scalar : Fin (nonzeroScalarCount width)) :
    incidenceAt (finProdFinEquiv (request, scalar)) = (request, scalar) := by
  exact Equiv.symm_apply_apply finProdFinEquiv (request, scalar)

/-- Complete structured slot key of one flat incidence. -/
noncomputable def scheduledIncidenceSlotAt
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    ResourceSlot groups dimension width :=
  scheduledIncidenceSlot widthPositive capacity output (incidenceAt incidence)

@[simp] theorem scheduledIncidenceSlotAt_finProdFinEquiv_first
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (request : Fin totalRequests)
    (scalar : Fin (nonzeroScalarCount width)) :
    (scheduledIncidenceSlotAt widthPositive capacity output
      (finProdFinEquiv (request, scalar))).1 =
        (requestGroupSlot capacity request).1 := by
  simp [scheduledIncidenceSlotAt, scheduledIncidenceSlot]

@[simp] theorem scheduledIncidenceSlotAt_finProdFinEquiv_second
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (request : Fin totalRequests)
    (scalar : Fin (nonzeroScalarCount width)) :
    (scheduledIncidenceSlotAt widthPositive capacity output
      (finProdFinEquiv (request, scalar))).2 =
        requestScheduledLinePoint widthPositive capacity output request
          scalar := by
  simp [scheduledIncidenceSlotAt, scheduledIncidenceSlot]

/-- Flat incidence keys inherit injectivity from the structured schedule. -/
theorem scheduledIncidenceSlotAt_injective
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : forall request scalar,
      requestScheduledLinePoint widthPositive capacity output
          request scalar =
        targets request + enumeratedNonzeroScalar scalar •
          normalizeBinaryExtensionVector (directions request).rep)
    (withinGroupDisjoint : forall left right,
      (requestGroupSlot capacity left).1 =
          (requestGroupSlot capacity right).1 ->
      left ≠ right ->
        Disjoint
          (requestScheduledLineSet widthPositive capacity output left)
          (requestScheduledLineSet widthPositive capacity output right)) :
    Function.Injective
      (scheduledIncidenceSlotAt widthPositive capacity output) := by
  intro left right equal
  apply finProdFinEquiv.symm.injective
  apply scheduledIncidenceSlot_injective widthPositive capacity output
    targets directions pointFormula withinGroupDisjoint
  exact equal

/-! ## Concrete Boolean routing keys and destinations -/

/-- Width of an active/padding marker followed by group and affine-point
bits. -/
@[reducible] def incidenceKeyWidth
    (groupBitWidth dimension width : Nat) : Nat :=
  (groupBitWidth + dimension * width) + 1

/-- Concrete marked Boolean key of a scheduled incidence. -/
noncomputable def scheduledIncidenceKeyBits
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) -> Bool :=
  activeRoutingKey
    (resourceSlotKeyBits widthPositive groupBitWidth
      (scheduledIncidenceSlotAt widthPositive capacity output incidence))

/-- Every structured resource slot occurs once in the destination array. -/
noncomputable def resourceDestinationKeyBits
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (destination : Fin (Nat.card
      (ResourceSlot groups dimension width))) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) -> Bool :=
  activeRoutingKey
    (resourceSlotKeyBits widthPositive groupBitWidth
      (resourceSlotAt destination))

/-- Destination index corresponding to one scheduled incidence. -/
noncomputable def incidenceDestination
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (Nat.card (ResourceSlot groups dimension width)) :=
  resourceSlotIndex
    (scheduledIncidenceSlotAt widthPositive capacity output incidence)

/-- All padding records share the reserved padding-marker key.  Repetition
among padding records is harmless because active destination keys use the
opposite marker. -/
def incidencePaddingKey
    (groupBitWidth dimension width : Nat) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) -> Bool :=
  paddingRoutingKey
    (fun _ : Fin (groupBitWidth + dimension * width) => false)

theorem scheduledIncidenceKeyBits_injective
    (widthPositive : 0 < width)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : forall request scalar,
      requestScheduledLinePoint widthPositive capacity output
          request scalar =
        targets request + enumeratedNonzeroScalar scalar •
          normalizeBinaryExtensionVector (directions request).rep)
    (withinGroupDisjoint : forall left right,
      (requestGroupSlot capacity left).1 =
          (requestGroupSlot capacity right).1 ->
      left ≠ right ->
        Disjoint
          (requestScheduledLineSet widthPositive capacity output left)
          (requestScheduledLineSet widthPositive capacity output right)) :
    Function.Injective
      (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
        output) := by
  intro left right equalKey
  apply scheduledIncidenceSlotAt_injective widthPositive capacity output
    targets directions pointFormula withinGroupDisjoint
  apply resourceSlotKeyBits_injective widthPositive groupFits
  exact activeRoutingKey_injective equalKey

theorem resourceDestinationKeyBits_injective
    (widthPositive : 0 < width)
    (groupFits : groups <= 2 ^ groupBitWidth) :
    Function.Injective
      (resourceDestinationKeyBits (groups := groups)
        (dimension := dimension) widthPositive groupBitWidth) := by
  intro left right equalKey
  apply (resourceSlotEquiv groups dimension width).symm.injective
  apply resourceSlotKeyBits_injective widthPositive groupFits
  exact activeRoutingKey_injective equalKey

@[simp] theorem resourceDestinationKeyBits_incidenceDestination
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    resourceDestinationKeyBits widthPositive groupBitWidth
        (incidenceDestination widthPositive capacity output incidence) =
      scheduledIncidenceKeyBits widthPositive groupBitWidth capacity output
        incidence := by
  simp [resourceDestinationKeyBits, incidenceDestination,
    scheduledIncidenceKeyBits]

theorem incidencePaddingKey_avoids
    (active : Fin (groupBitWidth + dimension * width) -> Bool) :
    incidencePaddingKey groupBitWidth dimension width ≠
      activeRoutingKey active := by
  exact paddingRoutingKey_ne_activeRoutingKey _ _

/-- Suffix payload carried by one flat scheduled incidence. -/
noncomputable def incidenceSourcePayload
    (requestPayload : Fin totalRequests -> Fin payloadWidth -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin payloadWidth -> Bool :=
  requestPayload (incidenceAt incidence).1

/-- Fully packed scatter input: scheduled incidences, one destination record
for every `(group, point)` slot, and reserved-marker padding records. -/
noncomputable def scatterRoutingInputBits
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (requestPayload : Fin totalRequests -> Fin payloadWidth -> Bool)
    (destinationPayload : Fin (Nat.card
      (ResourceSlot groups dimension width)) -> Fin payloadWidth -> Bool)
    (paddingPayload : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          Nat.card (ResourceSlot groups dimension width) + paddingCount =
        networkRecords routingDepth) :
    Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) payloadWidth)) ->
      Bool :=
  Routing.routingInputBits
    (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
      scheduleOutput)
    (incidenceSourcePayload requestPayload)
    (resourceDestinationKeyBits widthPositive groupBitWidth)
    destinationPayload
    (fun _ => incidencePaddingKey groupBitWidth dimension width)
    paddingPayload recordCount

/-- Concrete scatter theorem.  Every scheduled incidence sends exactly its
request suffix to the destination indexed by the incidence's `(group, point)`
slot key. -/
theorem scatterRoutingInputBits_routes_incidence
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
    (destinationPayload : Fin (Nat.card
      (ResourceSlot groups dimension width)) -> Fin payloadWidth -> Bool)
    (paddingPayload : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          Nat.card (ResourceSlot groups dimension width) + paddingCount =
        networkRecords routingDepth)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    let input := scatterRoutingInputBits widthPositive groupBitWidth capacity
      scheduleOutput requestPayload destinationPayload paddingPayload
      recordCount
    let sorted := bitonicSortBits
      (Routing.keyAndTagFitsRecord
        (incidenceKeyWidth groupBitWidth dimension width) payloadWidth)
      routingDepth true input
    exists destinationSorted,
      Routing.recordHasKeyTag
          (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
            scheduleOutput incidence) true
          (flatRecords sorted destinationSorted) /\
        Routing.recordPayload
            ((Routing.sortedPredecessorCopyCircuit routingDepth
              (incidenceKeyWidth groupBitWidth dimension width) payloadWidth
              false true).eval DeMorgan.interpretation input)
            destinationSorted =
          requestPayload (incidenceAt incidence).1 := by
  exact Routing.routingInputBits_routes_source_payload
    (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
      scheduleOutput)
    (incidenceSourcePayload requestPayload)
    (resourceDestinationKeyBits widthPositive groupBitWidth)
    destinationPayload
    (fun _ => incidencePaddingKey groupBitWidth dimension width)
    paddingPayload
    (scheduledIncidenceKeyBits_injective widthPositive groupFits capacity
      scheduleOutput targets directions pointFormula withinGroupDisjoint)
    (resourceDestinationKeyBits_injective widthPositive groupFits)
    (incidenceDestination widthPositive capacity scheduleOutput)
    (resourceDestinationKeyBits_incidenceDestination widthPositive
      groupBitWidth capacity scheduleOutput)
    (fun _padding source => incidencePaddingKey_avoids
      (resourceSlotKeyBits widthPositive groupBitWidth
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          source)))
    recordCount incidence

/-! ## Full key-space slot arrays for canonical ordering -/

/-- Destination key at a canonical lexicographic position in the complete
unmarked key space.  Provisioning the full key space costs at most the usual
power-of-two rounding factor once `groupBitWidth` is chosen minimally. -/
noncomputable def fullResourceDestinationKeyBits
    (groupBitWidth dimension width : Nat)
    (destination : Fin (2 ^ (groupBitWidth + dimension * width))) :
    Fin (incidenceKeyWidth groupBitWidth dimension width) -> Bool :=
  activeRoutingKey (lexBitVectorAt destination)

/-- Canonical full-key-space destination of one scheduled incidence. -/
noncomputable def fullIncidenceDestination
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (2 ^ (groupBitWidth + dimension * width)) :=
  lexBitVectorIndex
    (resourceSlotKeyBits widthPositive groupBitWidth
      (scheduledIncidenceSlotAt widthPositive capacity output incidence))

theorem fullResourceDestinationKeyBits_injective :
    Function.Injective
      (fullResourceDestinationKeyBits groupBitWidth dimension width) := by
  intro left right equal
  apply lexBitVectorAt_injective
  exact activeRoutingKey_injective equal

@[simp] theorem fullResourceDestinationKeyBits_fullIncidenceDestination
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    fullResourceDestinationKeyBits groupBitWidth dimension width
        (fullIncidenceDestination widthPositive groupBitWidth capacity output
          incidence) =
      scheduledIncidenceKeyBits widthPositive groupBitWidth capacity output
        incidence := by
  simp [fullResourceDestinationKeyBits, fullIncidenceDestination,
    scheduledIncidenceKeyBits]

/-- Packed scatter input with one destination for every possible active key.
This variant makes the destination prefix after canonical sorting completely
independent of the run-time incidence subset. -/
noncomputable def fullScatterRoutingInputBits
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
  Routing.routingInputBits
    (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
      scheduleOutput)
    (incidenceSourcePayload requestPayload)
    (fullResourceDestinationKeyBits groupBitWidth dimension width)
    destinationPayload
    (fun _ => incidencePaddingKey groupBitWidth dimension width)
    paddingPayload recordCount

/-- Every incidence is routed correctly in the full-key-space scatter
layout. -/
theorem fullScatterRoutingInputBits_routes_incidence
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
    let input := fullScatterRoutingInputBits widthPositive groupBitWidth
      capacity scheduleOutput requestPayload destinationPayload
      paddingPayload recordCount
    let sorted := bitonicSortBits
      (Routing.keyAndTagFitsRecord
        (incidenceKeyWidth groupBitWidth dimension width) payloadWidth)
      routingDepth true input
    exists destinationSorted,
      Routing.recordHasKeyTag
          (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
            scheduleOutput incidence) true
          (flatRecords sorted destinationSorted) /\
        Routing.recordPayload
            ((Routing.sortedPredecessorCopyCircuit routingDepth
              (incidenceKeyWidth groupBitWidth dimension width) payloadWidth
              false true).eval DeMorgan.interpretation input)
            destinationSorted =
          requestPayload (incidenceAt incidence).1 := by
  exact Routing.routingInputBits_routes_source_payload
    (scheduledIncidenceKeyBits widthPositive groupBitWidth capacity
      scheduleOutput)
    (incidenceSourcePayload requestPayload)
    (fullResourceDestinationKeyBits groupBitWidth dimension width)
    destinationPayload
    (fun _ => incidencePaddingKey groupBitWidth dimension width)
    paddingPayload
    (scheduledIncidenceKeyBits_injective widthPositive groupFits capacity
      scheduleOutput targets directions pointFormula withinGroupDisjoint)
    fullResourceDestinationKeyBits_injective
    (fullIncidenceDestination widthPositive groupBitWidth capacity
      scheduleOutput)
    (fullResourceDestinationKeyBits_fullIncidenceDestination widthPositive
      groupBitWidth capacity scheduleOutput)
    (fun _padding source => incidencePaddingKey_avoids
      (resourceSlotKeyBits widthPositive groupBitWidth
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          source)))
    recordCount incidence

end IncidenceRouting
end MassProduction
end Algebraic
