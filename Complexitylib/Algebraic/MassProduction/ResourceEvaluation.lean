/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CanonicalScatter
public import Complexitylib.Algebraic.MassProduction.GatherRouting
public import Complexitylib.Algebraic.MassProduction.ResourcePacking

/-!
# Parallel evaluation of shorter resource functions

After scatter, each canonical `(group, point)` record contains one suffix.
For every affine point and every field-basis coordinate, this module wires
those group slots into one supplied mass-production circuit for the shorter
Boolean resource function.  All wiring is explicit and costs no gates.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace ResourceEvaluation

universe u

variable {Prefix : Type u}

open scoped LinearAlgebra.Projectivization
open CanonicalScatter
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open RoutingMetadata
open SchedulerIteration
open Sorting

/-- Number of raw affine-point bit vectors. -/
@[reducible] def pointCount (dimension width : Nat) : Nat :=
  2 ^ (dimension * width)

/-- One resource member for every `(point, field bit)` pair. -/
@[reducible] def resourceBitCount (dimension width : Nat) : Nat :=
  pointCount dimension width * width

/-- Row-major resource-member index. -/
def resourceMemberIndex
    (point : Fin (pointCount dimension width))
    (bit : Fin width) : Fin (resourceBitCount dimension width) :=
  finProdFinEquiv (point, bit)

/-- Decode a resource-member index. -/
def resourceMemberAt
    (member : Fin (resourceBitCount dimension width)) :
    Fin (pointCount dimension width) × Fin width :=
  finProdFinEquiv.symm member

@[simp] theorem resourceMemberAt_index
    (point : Fin (pointCount dimension width))
    (bit : Fin width) :
    resourceMemberAt (resourceMemberIndex point bit) = (point, bit) := by
  exact Equiv.symm_apply_apply finProdFinEquiv (point, bit)

/-- Canonical full-key-space destination for a valid group and raw point-bit
vector. -/
noncomputable def resourceSlotDestination
    (groupBitWidth dimension width : Nat)
    (group : Fin groups)
    (point : Fin (pointCount dimension width)) :
    Fin (2 ^ (groupBitWidth + dimension * width)) :=
  lexBitVectorIndex
    (Fin.append (finiteIndexBits groupBitWidth group)
      (lexBitVectorAt point))

@[simp] theorem lexBitVectorAt_resourceSlotDestination
    (group : Fin groups)
    (point : Fin (pointCount dimension width)) :
    lexBitVectorAt
        (resourceSlotDestination groupBitWidth dimension width group point) =
      Fin.append (finiteIndexBits groupBitWidth group)
        (lexBitVectorAt point) := by
  exact lexBitVectorAt_index _

/-- Raw point-bit index of one scheduled incidence. -/
noncomputable def scheduledIncidencePointIndex
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    Fin (pointCount dimension width) :=
  lexBitVectorIndex
    (binaryExtensionVectorBits widthPositive
      (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
        incidence).2)

@[simp] theorem lexBitVectorAt_scheduledIncidencePointIndex
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    lexBitVectorAt
        (scheduledIncidencePointIndex widthPositive capacity scheduleOutput
          incidence) =
      binaryExtensionVectorBits widthPositive
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          incidence).2 := by
  exact lexBitVectorAt_index _

/-- Decoding the scheduled point index returns the geometric incidence
point. -/
theorem pointCoordinate_scheduledIncidencePointIndex
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    binaryExtensionVectorCoordinate widthPositive
        (lexBitVectorAt
          (scheduledIncidencePointIndex widthPositive capacity scheduleOutput
            incidence)) =
      (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
        incidence).2 := by
  rw [lexBitVectorAt_scheduledIncidencePointIndex]
  funext coordinate
  rw [binaryExtensionVectorCoordinate_vectorBits]

/-- The separately decoded group and point indices identify exactly the same
full scatter slot as the incidence key. -/
theorem resourceSlotDestination_scheduledIncidence
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    resourceSlotDestination groupBitWidth dimension width
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          incidence).1
        (scheduledIncidencePointIndex widthPositive capacity scheduleOutput
          incidence) =
      fullIncidenceDestination widthPositive groupBitWidth capacity
        scheduleOutput incidence := by
  unfold resourceSlotDestination fullIncidenceDestination
    scheduledIncidencePointIndex resourceSlotKeyBits
  rw [lexBitVectorAt_index]

/-- Physical scatter-output wire used as one local resource-circuit input. -/
noncomputable def resourceCircuitInputIndex
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth)
    (member : Fin (resourceBitCount dimension width))
    (input : Fin (groups * suffixWidth)) :
    Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) :=
  let memberFields := resourceMemberAt member
  let inputFields := finProdFinEquiv.symm input
  Routing.recordBitIndex routingDepth
    (incidenceKeyWidth groupBitWidth dimension width) suffixWidth
    (Fin.castLE destinationFits
      (resourceSlotDestination groupBitWidth dimension width
        inputFields.1 memberFields.1))
    (Routing.payloadBit
      (incidenceKeyWidth groupBitWidth dimension width) suffixWidth
      inputFields.2)

/-- Put every supplied `groups`-copy resource circuit in parallel and wire
its inputs directly to the corresponding fixed scatter slots. -/
noncomputable def resourceBankCircuit
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups) :
    Circuit DeMorgan.signature
      (networkBits routingDepth
        (Routing.recordWidth
          (incidenceKeyWidth groupBitWidth dimension width) suffixWidth))
      (resourceBitCount dimension width * groups) :=
  Circuit.parallelFinVector (resourceBitCount dimension width) groups fun member =>
      (resourceCircuits member).mapInputs
        (resourceCircuitInputIndex destinationFits member)

/-- The bank has exactly the resource circuits' gates combined; routing each circuit to its
destination block is pure wiring. -/
@[simp] theorem resourceBankCircuit_size
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups) :
    (resourceBankCircuit destinationFits resourceCircuits).size =
      ∑ member, (resourceCircuits member).size := by
  simp [resourceBankCircuit]

@[simp] theorem resourceBankCircuit_eval_apply
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (scatterOutput : Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool)
    (point : Fin (pointCount dimension width))
    (bit : Fin width)
    (group : Fin groups) :
    (resourceBankCircuit destinationFits resourceCircuits).eval
        DeMorgan.interpretation scatterOutput
        (finProdFinEquiv (resourceMemberIndex point bit, group)) =
      (resourceCircuits (resourceMemberIndex point bit)).eval
        DeMorgan.interpretation
        (scatterOutput ∘ resourceCircuitInputIndex destinationFits
          (resourceMemberIndex point bit)) group := by
  rw [resourceBankCircuit, Circuit.eval_parallelFinVector,
    Circuit.eval_mapInputs]

/-- Exact bank cost: resource circuits share no gates with one another, while
the fixed input wiring is free. -/
@[simp] theorem resourceBankCircuit_cost
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups) :
    (resourceBankCircuit destinationFits resourceCircuits).cost
        DeMorgan.standardCost =
      ∑ member, (resourceCircuits member).cost DeMorgan.standardCost := by
  rw [resourceBankCircuit, Circuit.cost_parallelFinVector]
  apply Finset.sum_congr rfl
  intro member _member
  simp

/-! ## Incidence semantics -/

set_option maxHeartbeats 800000 in
/-- A resource circuit sees the suffix routed to its fixed `(group, point)`
slot.  Hence its output for a scheduled incidence is the corresponding
shorter resource function evaluated on that request's suffix. -/
theorem resourceBankCircuit_eval_incidence
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
    (requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool)
    (destinationSuffix :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin suffixWidth -> Bool)
    (paddingSuffix : Fin paddingCount -> Fin suffixWidth -> Bool)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (resourceFunctions : Fin (pointCount dimension width) -> Fin width ->
      ScalarFunction Bool suffixWidth)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct (resourceFunctions point bit) groups))
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (bit : Fin width) :
    let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
      capacity scheduleOutput requestSuffix destinationSuffix paddingSuffix
      recordCount
    let destinationFits :
        2 ^ (groupBitWidth + dimension * width) <=
          networkRecords routingDepth := by
      rw [← recordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    let point := scheduledIncidencePointIndex widthPositive capacity
      scheduleOutput incidence
    let group := (scheduledIncidenceSlotAt widthPositive capacity
      scheduleOutput incidence).1
    (resourceBankCircuit destinationFits resourceCircuits).eval
        DeMorgan.interpretation scatterOutput
        (finProdFinEquiv (resourceMemberIndex point bit, group)) =
      resourceFunctions point bit
        (requestSuffix (incidenceAt incidence).1) := by
  dsimp only
  let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
    capacity scheduleOutput requestSuffix destinationSuffix paddingSuffix
    recordCount
  have destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth := by
    rw [← recordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  let point := scheduledIncidencePointIndex widthPositive capacity
    scheduleOutput incidence
  let group := (scheduledIncidenceSlotAt widthPositive capacity
    scheduleOutput incidence).1
  let selectedInput : Fin (groups * suffixWidth) -> Bool := scatterOutput ∘
    resourceCircuitInputIndex destinationFits
      (resourceMemberIndex point bit)
  rw [resourceBankCircuit_eval_apply]
  have computed := congrFun (computes point bit selectedInput) group
  change
    (resourceCircuits (resourceMemberIndex point bit)).eval
        DeMorgan.interpretation selectedInput group =
      resourceFunctions point bit
        (directProductInput selectedInput group) at computed
  rw [computed]
  apply congrArg (resourceFunctions point bit)
  funext suffixBit
  have scattered := canonicalFullScatterBits_routes_incidence
    widthPositive groupFits capacity scheduleOutput targets directions
    pointFormula withinGroupDisjoint requestSuffix destinationSuffix
    paddingSuffix recordCount incidence
  dsimp only at scattered
  have scatteredBit := congrFun scattered suffixBit
  change scatterOutput
      (resourceCircuitInputIndex destinationFits
        (resourceMemberIndex point bit)
        (finProdFinEquiv (group, suffixBit))) =
    requestSuffix (incidenceAt incidence).1 suffixBit
  simp only [resourceCircuitInputIndex, resourceMemberAt_index,
    Equiv.symm_apply_apply]
  change Routing.recordPayload scatterOutput
      (Fin.castLE destinationFits
        (resourceSlotDestination groupBitWidth dimension width group point))
      suffixBit = requestSuffix (incidenceAt incidence).1 suffixBit
  rw [resourceSlotDestination_scheduledIncidence widthPositive groupBitWidth
    capacity scheduleOutput incidence]
  exact scatteredBit

/-! ## Viewing bank outputs as a complete source-slot array -/

/-- Group-prefix bits of one canonical full-key destination. -/
noncomputable def fullDestinationGroupBits
    (groupBitWidth pointWidth : Nat)
    (destination : Fin (2 ^ (groupBitWidth + pointWidth))) :
    Fin groupBitWidth -> Bool :=
  fun bit => lexBitVectorAt destination (Fin.castAdd pointWidth bit)

/-- Point-suffix bits of one canonical full-key destination. -/
noncomputable def fullDestinationPointBits
    (groupBitWidth pointWidth : Nat)
    (destination : Fin (2 ^ (groupBitWidth + pointWidth))) :
    Fin pointWidth -> Bool :=
  fun bit => lexBitVectorAt destination (Fin.natAdd groupBitWidth bit)

@[simp] theorem fullDestinationGroupBits_resourceSlotDestination
    (group : Fin groups)
    (point : Fin (pointCount dimension width)) :
    fullDestinationGroupBits groupBitWidth (dimension * width)
        (resourceSlotDestination groupBitWidth dimension width group point) =
      finiteIndexBits groupBitWidth group := by
  funext bit
  simp [fullDestinationGroupBits]

@[simp] theorem fullDestinationPointBits_resourceSlotDestination
    (group : Fin groups)
    (point : Fin (pointCount dimension width)) :
    fullDestinationPointBits groupBitWidth (dimension * width)
        (resourceSlotDestination groupBitWidth dimension width group point) =
      lexBitVectorAt point := by
  funext bit
  simp [fullDestinationPointBits]

/-- Decode a valid group encoding; unused raw encodings are sent to group
zero.  This is a nonuniform wire-selection function, not a circuit or an
instance. -/
noncomputable def decodedGroupOrZero
    (groupsPositive : 0 < groups)
    (groupBitWidth : Nat)
    (bits : Fin groupBitWidth -> Bool) : Fin groups := by
  classical
  exact if represented : ∃ group,
      finiteIndexBits groupBitWidth group = bits then
    Classical.choose represented
  else
    ⟨0, groupsPositive⟩

@[simp] theorem decodedGroupOrZero_finiteIndexBits
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (group : Fin groups) :
    decodedGroupOrZero groupsPositive groupBitWidth
        (finiteIndexBits groupBitWidth group) = group := by
  classical
  unfold decodedGroupOrZero
  split
  · rename_i represented
    apply finiteIndexBits_injective groupFits
    exact Classical.choose_spec represented
  · rename_i represented
    exact False.elim (represented ⟨group, rfl⟩)

/-- Point-member index decoded from a complete canonical destination. -/
noncomputable def fullDestinationPointIndex
    (groupBitWidth dimension width : Nat)
    (destination : Fin (2 ^ (groupBitWidth + dimension * width))) :
    Fin (pointCount dimension width) :=
  lexBitVectorIndex
    (fullDestinationPointBits groupBitWidth (dimension * width) destination)

@[simp] theorem fullDestinationPointIndex_resourceSlotDestination
    (group : Fin groups)
    (point : Fin (pointCount dimension width)) :
    fullDestinationPointIndex groupBitWidth dimension width
        (resourceSlotDestination groupBitWidth dimension width group point) =
      point := by
  unfold fullDestinationPointIndex
  rw [fullDestinationPointBits_resourceSlotDestination,
    lexBitVectorIndex_at]

/-- Interpret a resource-bank output as one value for every raw full-key
source slot.  Invalid group encodings may select an arbitrary group-zero
value because no scheduled incidence can request them. -/
noncomputable def resourceValuesFromBank
    (groupsPositive : 0 < groups)
    (groupBitWidth dimension width : Nat)
    (bankOutput : Fin (resourceBitCount dimension width * groups) -> Bool)
    (destination : Fin (2 ^ (groupBitWidth + dimension * width))) :
    Fin width -> Bool :=
  fun bit => bankOutput (finProdFinEquiv
    (resourceMemberIndex
      (fullDestinationPointIndex groupBitWidth dimension width destination)
      bit,
    decodedGroupOrZero groupsPositive groupBitWidth
      (fullDestinationGroupBits groupBitWidth (dimension * width)
        destination)))

@[simp] theorem resourceValuesFromBank_resourceSlotDestination
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (bankOutput : Fin (resourceBitCount dimension width * groups) -> Bool)
    (group : Fin groups)
    (point : Fin (pointCount dimension width)) :
    resourceValuesFromBank groupsPositive groupBitWidth dimension width
        bankOutput
        (resourceSlotDestination groupBitWidth dimension width group point) =
      fun bit => bankOutput
        (finProdFinEquiv (resourceMemberIndex point bit, group)) := by
  funext bit
  simp [resourceValuesFromBank, groupFits]

/-- In particular, the total source-slot view selects the actual incidence's
group and point bank output. -/
theorem resourceValuesFromBank_fullIncidenceDestination
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (bankOutput : Fin (resourceBitCount dimension width * groups) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    resourceValuesFromBank groupsPositive groupBitWidth dimension width
        bankOutput
        (fullIncidenceDestination widthPositive groupBitWidth capacity
          scheduleOutput incidence) =
      fun bit => bankOutput (finProdFinEquiv
        (resourceMemberIndex
          (scheduledIncidencePointIndex widthPositive capacity scheduleOutput
            incidence) bit,
        (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
          incidence).1)) := by
  rw [← resourceSlotDestination_scheduledIncidence widthPositive
    groupBitWidth capacity scheduleOutput incidence]
  exact resourceValuesFromBank_resourceSlotDestination groupsPositive
    groupFits bankOutput _ _

/-- Complete resource-source values obtained by evaluating the wired bank on
one fixed scatter output. -/
noncomputable def evaluatedResourceValues
    (groupsPositive : 0 < groups)
    (groupBitWidth dimension width routingDepth suffixWidth : Nat)
    (destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (scatterOutput : Fin (networkBits routingDepth
      (Routing.recordWidth
        (incidenceKeyWidth groupBitWidth dimension width) suffixWidth)) ->
      Bool) :
    Fin (2 ^ (groupBitWidth + dimension * width)) -> Fin width -> Bool :=
  resourceValuesFromBank groupsPositive groupBitWidth dimension width
    ((resourceBankCircuit destinationFits resourceCircuits).eval
      DeMorgan.interpretation scatterOutput)

set_option maxHeartbeats 800000 in
/-- The complete source-slot view of the bank agrees with the intended
shorter resource function on every actually scheduled incidence. -/
theorem evaluatedResourceValues_routes_incidence
    (widthPositive : 0 < width)
    (groupsPositive : 0 < groups)
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
    (requestSuffix : Fin totalRequests -> Fin suffixWidth -> Bool)
    (destinationSuffix :
      Fin (2 ^ (groupBitWidth + dimension * width)) ->
        Fin suffixWidth -> Bool)
    (paddingSuffix : Fin paddingCount -> Fin suffixWidth -> Bool)
    (recordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + paddingCount =
        networkRecords routingDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (resourceFunctions : Fin (pointCount dimension width) -> Fin width ->
      ScalarFunction Bool suffixWidth)
    (computes : forall point bit,
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct (resourceFunctions point bit) groups))
    (incidence : Fin (totalRequests * nonzeroScalarCount width)) :
    let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
      capacity scheduleOutput requestSuffix destinationSuffix paddingSuffix
      recordCount
    let destinationFits :
        2 ^ (groupBitWidth + dimension * width) <=
          networkRecords routingDepth := by
      rw [← recordCount]
      exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    evaluatedResourceValues groupsPositive groupBitWidth dimension width
        routingDepth suffixWidth destinationFits resourceCircuits
        scatterOutput
        (fullIncidenceDestination widthPositive groupBitWidth capacity
          scheduleOutput incidence) =
      fun bit => resourceFunctions
        (scheduledIncidencePointIndex widthPositive capacity scheduleOutput
          incidence) bit
        (requestSuffix (incidenceAt incidence).1) := by
  dsimp only
  let scatterOutput := canonicalFullScatterBits widthPositive groupBitWidth
    capacity scheduleOutput requestSuffix destinationSuffix paddingSuffix
    recordCount
  have destinationFits :
      2 ^ (groupBitWidth + dimension * width) <=
        networkRecords routingDepth := by
    rw [← recordCount]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  funext bit
  rw [evaluatedResourceValues,
    resourceValuesFromBank_fullIncidenceDestination widthPositive
      groupsPositive groupFits capacity scheduleOutput]
  exact resourceBankCircuit_eval_incidence widthPositive groupFits capacity
    scheduleOutput targets directions pointFormula withinGroupDisjoint
    requestSuffix destinationSuffix paddingSuffix recordCount
    resourceCircuits resourceFunctions computes incidence bit

/-! ## Packed evaluation-code resources -/

/-- Boolean resource function for one affine point and one field-basis bit. -/
noncomputable def packedResourceFunction
    (widthPositive : 0 < width)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (point : Fin (pointCount dimension width))
    (bit : Fin width) : ScalarFunction Bool suffixWidth :=
  fun suffix =>
    decodeBinaryExtension widthPositive
      (packedEvaluationResource widthPositive placement function
        (binaryExtensionVectorCoordinate widthPositive
          (lexBitVectorAt point)) suffix)
      bit

/-- At an incidence point, the indexed resource function is exactly the
selected basis bit of the manuscript's field-valued resource. -/
theorem packedResourceFunction_scheduledIncidencePoint
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (scheduleOutput : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> (Fin suffixWidth -> Bool) -> Bool)
    (incidence : Fin (totalRequests * nonzeroScalarCount width))
    (bit : Fin width)
    (suffix : Fin suffixWidth -> Bool) :
    packedResourceFunction widthPositive placement function
        (scheduledIncidencePointIndex widthPositive capacity scheduleOutput
          incidence) bit suffix =
      decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function
          (scheduledIncidenceSlotAt widthPositive capacity scheduleOutput
            incidence).2 suffix)
        bit := by
  unfold packedResourceFunction
  rw [pointCoordinate_scheduledIncidencePointIndex]

end ResourceEvaluation
end MassProduction
end Algebraic
