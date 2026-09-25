/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SchedulerIteration
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Parallel request-group scheduling

The manuscript permits a resource coordinate to be reused across different
request groups, while requiring punctured recovery lines to be disjoint inside
each group.  This module realizes that exact rectangular construction by
replicating the verified greedy scheduler on disjoint group input blocks.

The group count and group size are ordinary natural parameters.  In
particular, no finite-type or field instances are exported by this layer.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace GroupedScheduler

open scoped LinearAlgebra.Projectivization
open LineEnumeration
open SchedulerIteration
open Sorting

/-- Row-major target bits for a rectangular `(group, request)` family. -/
noncomputable def groupedTargetArrayBits
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :
    Fin (groups *
      (requestsPerGroup * pointBitWidth dimension width)) -> Bool :=
  fun flat =>
    let groupAndBit := (finProdFinEquiv
      (m := groups)
      (n := requestsPerGroup * pointBitWidth dimension width)).symm flat
    targetArrayBits widthPositive (targets groupAndBit.1) groupAndBit.2

@[simp] theorem directProductInput_groupedTargetArrayBits
    (widthPositive : 0 < width)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width)
    (group : Fin groups) :
    directProductInput (groupedTargetArrayBits widthPositive targets) group =
      targetArrayBits widthPositive (targets group) := by
  funext bit
  unfold directProductInput groupedTargetArrayBits
  rw [Equiv.symm_apply_apply]

/-- One independent greedy scheduler per request group. -/
noncomputable def groupedScheduleCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth groups requestsPerGroup : Nat)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords depth) :
    Circuit DeMorgan.signature
      (groups * (requestsPerGroup * pointBitWidth dimension width))
      (groups *
        greedyScheduleGateCount dimension widthPositive depth
          requestsPerGroup)
      (groups * (requestsPerGroup * lineBitWidth dimension width)) :=
  (greedyScheduleCircuit dimension widthPositive depth requestsPerGroup
    allFit).replicate groups

/-- Evaluate all group schedulers on the rectangular target family. -/
noncomputable def groupedScheduleOutput
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth groups requestsPerGroup : Nat)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords depth)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :
    Fin (groups * (requestsPerGroup * lineBitWidth dimension width)) -> Bool :=
  (groupedScheduleCircuit dimension widthPositive depth groups
    requestsPerGroup allFit).eval DeMorgan.interpretation
      (groupedTargetArrayBits widthPositive targets)

/-- Select the schedule-output block belonging to one group. -/
noncomputable def groupScheduleBits
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (group : Fin groups) :
    Fin (requestsPerGroup * lineBitWidth dimension width) -> Bool :=
  directProductInput output group

/-- Replication evaluates the verified one-group scheduler independently on
the selected group target block. -/
theorem groupScheduleBits_groupedScheduleOutput
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords depth)
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width)
    (group : Fin groups) :
    groupScheduleBits
        (groupedScheduleOutput dimension widthPositive depth groups
          requestsPerGroup allFit targets) group =
      greedyScheduleOutput dimension widthPositive depth requestsPerGroup
        allFit (targets group) := by
  funext output
  unfold groupScheduleBits groupedScheduleOutput groupedScheduleCircuit
  unfold directProductInput
  rw [Circuit.eval_replicate_apply]
  unfold greedyScheduleOutput
  rw [directProductInput_groupedTargetArrayBits]

/-- Exact grouped scheduler invariant: every output is a punctured affine
line through its target, and lines are pairwise disjoint within each group.
No disjointness is asserted across groups, matching the bounded-demand
construction. -/
theorem groupedScheduleCircuit_correct
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords depth)
    (capacity : requestsPerGroup * nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (targets : Fin groups -> Fin requestsPerGroup ->
      Fin dimension -> BinaryExtension width) :
    let output := groupedScheduleOutput dimension widthPositive depth groups
      requestsPerGroup allFit targets
    exists directions : Fin groups -> Fin requestsPerGroup ->
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width),
      (forall group request scalar,
        scheduledLinePoint widthPositive
            (groupScheduleBits output group) request scalar =
          targets group request + enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector
              (directions group request).rep) /\
      (forall group request,
        scheduledLineSet widthPositive
            (groupScheduleBits output group) request =
          ForbiddenRanks.binaryExtensionPuncturedLine
            (targets group request) (directions group request)) /\
      (forall group,
        PairwiseDisjointFamily
          (scheduledLineSet widthPositive
            (groupScheduleBits output group))) := by
  dsimp only
  classical
  choose directions pointCorrect setCorrect pairwise using
    fun group => greedyScheduleCircuit_correct widthPositive widthAtLeastTwo
      requestsPerGroup allFit capacity (targets group)
  refine ⟨directions, ?_, ?_, ?_⟩
  · intro group request scalar
    rw [groupScheduleBits_groupedScheduleOutput]
    exact pointCorrect group request scalar
  · intro group request
    rw [groupScheduleBits_groupedScheduleOutput]
    exact setCorrect group request
  · intro group
    rw [groupScheduleBits_groupedScheduleOutput]
    exact pairwise group

/-- Replication charges exactly one scheduler cost per group. -/
theorem groupedScheduleCircuit_cost
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords depth) :
    (groupedScheduleCircuit dimension widthPositive depth groups
      requestsPerGroup allFit).cost DeMorgan.standardCost =
      groups *
        (greedyScheduleCircuit dimension widthPositive depth
          requestsPerGroup allFit).cost DeMorgan.standardCost := by
  simp [groupedScheduleCircuit]

/-- The finite grouped cost ledger: `groups * requestsPerGroup` copies of the
fixed-capacity scheduler/enumerator stage. -/
theorem groupedScheduleCircuit_cost_le
    (widthPositive : 0 < width)
    (allFit : requestsPerGroup * nonzeroScalarCount width <=
      networkRecords depth) :
    (groupedScheduleCircuit dimension widthPositive depth groups
      requestsPerGroup allFit).cost DeMorgan.standardCost <=
      groups * requestsPerGroup *
        scheduledLineEnumerationCostBound dimension width depth := by
  rw [groupedScheduleCircuit_cost widthPositive allFit]
  calc
    groups *
        (greedyScheduleCircuit dimension widthPositive depth
          requestsPerGroup allFit).cost DeMorgan.standardCost <=
        groups * (requestsPerGroup *
          scheduledLineEnumerationCostBound dimension width depth) :=
      Nat.mul_le_mul_left groups
        (greedyScheduleCircuit_cost_le widthPositive requestsPerGroup allFit)
    _ = groups * requestsPerGroup *
        scheduledLineEnumerationCostBound dimension width depth := by ring

/-! ## Padding an arbitrary request count into fixed groups -/

/-- Maximum group size for `totalRequests` requests split over a positive
number of groups. -/
def requestGroupSize (totalRequests groups : Nat) : Nat :=
  totalRequests ⌈/⌉ groups

/-- The rectangular group array has room for every real request. -/
theorem requestGroupCapacity
    (groupsPositive : 0 < groups) :
    totalRequests <= groups * requestGroupSize totalRequests groups := by
  unfold requestGroupSize
  exact (ceilDiv_le_iff_le_mul groupsPositive).1 le_rfl

/-- Rectangular `(group, local request)` position assigned to one real
request by row-major order. -/
def requestGroupSlot
    (capacity : totalRequests <= groups * requestsPerGroup)
    (request : Fin totalRequests) : Fin groups × Fin requestsPerGroup :=
  finProdFinEquiv.symm (Fin.castLE capacity request)

/-- Pad unused rectangular request slots with an arbitrary fixed target. -/
def paddedGroupedTargets
    (_capacity : totalRequests <= groups * requestsPerGroup)
    (targets : Fin totalRequests -> pointType)
    (dummy : pointType) : Fin groups -> Fin requestsPerGroup -> pointType :=
  fun group request =>
    let flat := finProdFinEquiv (group, request)
    if live : flat.val < totalRequests then
      targets ⟨flat.val, live⟩
    else
      dummy

/-- Padding leaves every real request at its assigned rectangular slot. -/
@[simp] theorem paddedGroupedTargets_at_request
    (capacity : totalRequests <= groups * requestsPerGroup)
    (targets : Fin totalRequests -> pointType)
    (dummy : pointType)
    (request : Fin totalRequests) :
    paddedGroupedTargets capacity targets dummy
        (requestGroupSlot capacity request).1
        (requestGroupSlot capacity request).2 =
      targets request := by
  unfold paddedGroupedTargets requestGroupSlot
  rw [Equiv.apply_symm_apply]
  simp only [Fin.castLE, request.isLt, dite_true]

/-- Decode one real request's point from the padded grouped output. -/
noncomputable def requestScheduledLinePoint
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (request : Fin totalRequests)
    (scalar : Fin (nonzeroScalarCount width)) :
    Fin dimension -> BinaryExtension width :=
  scheduledLinePoint widthPositive
    (groupScheduleBits output (requestGroupSlot capacity request).1)
    (requestGroupSlot capacity request).2 scalar

/-- Recovery set decoded for one real request in a padded grouped output. -/
noncomputable def requestScheduledLineSet
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (request : Fin totalRequests) :
    Finset (Fin dimension -> BinaryExtension width) :=
  scheduledLineSet widthPositive
    (groupScheduleBits output (requestGroupSlot capacity request).1)
    (requestGroupSlot capacity request).2

/-- Arbitrary request counts inherit exact line recovery and within-group
disjointness after padding to `groups * ceil(totalRequests / groups)` slots. -/
theorem paddedGroupedScheduleCircuit_correct
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (groupsPositive : 0 < groups)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= networkRecords depth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (dummy : Fin dimension -> BinaryExtension width) :
    let groupSize := requestGroupSize totalRequests groups
    let capacity := requestGroupCapacity
      (totalRequests := totalRequests) groupsPositive
    let paddedTargets := paddedGroupedTargets capacity targets dummy
    let output := groupedScheduleOutput dimension widthPositive depth groups
      groupSize allFit paddedTargets
    exists directions : Fin totalRequests ->
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width),
      (forall request scalar,
        requestScheduledLinePoint widthPositive capacity output
            request scalar =
          targets request + enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector (directions request).rep) /\
      (forall request,
        requestScheduledLineSet widthPositive capacity output request =
          ForbiddenRanks.binaryExtensionPuncturedLine
            (targets request) (directions request)) /\
      (forall left right,
        (requestGroupSlot capacity left).1 =
            (requestGroupSlot capacity right).1 ->
        left ≠ right ->
          Disjoint
            (requestScheduledLineSet widthPositive capacity output left)
            (requestScheduledLineSet widthPositive capacity output right)) := by
  dsimp only
  let groupSize := requestGroupSize totalRequests groups
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  let paddedTargets : Fin groups -> Fin groupSize ->
      Fin dimension -> BinaryExtension width :=
    paddedGroupedTargets capacity targets dummy
  let output := groupedScheduleOutput dimension widthPositive depth groups
    groupSize allFit paddedTargets
  obtain ⟨rectangularDirections, pointCorrect, setCorrect,
      pairwise⟩ :=
    groupedScheduleCircuit_correct widthPositive widthAtLeastTwo allFit
      directionCapacity paddedTargets
  let directions : Fin totalRequests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width) :=
    fun request =>
      rectangularDirections (requestGroupSlot capacity request).1
        (requestGroupSlot capacity request).2
  refine ⟨directions, ?_, ?_, ?_⟩
  · intro request scalar
    change scheduledLinePoint widthPositive
        (groupScheduleBits output (requestGroupSlot capacity request).1)
        (requestGroupSlot capacity request).2 scalar =
      targets request + enumeratedNonzeroScalar scalar •
        normalizeBinaryExtensionVector
          (rectangularDirections (requestGroupSlot capacity request).1
            (requestGroupSlot capacity request).2).rep
    have correct := pointCorrect (requestGroupSlot capacity request).1
      (requestGroupSlot capacity request).2 scalar
    rw [show paddedTargets (requestGroupSlot capacity request).1
        (requestGroupSlot capacity request).2 = targets request by
      exact paddedGroupedTargets_at_request capacity targets dummy request]
      at correct
    exact correct
  · intro request
    change scheduledLineSet widthPositive
        (groupScheduleBits output (requestGroupSlot capacity request).1)
        (requestGroupSlot capacity request).2 =
      ForbiddenRanks.binaryExtensionPuncturedLine (targets request)
        (rectangularDirections (requestGroupSlot capacity request).1
          (requestGroupSlot capacity request).2)
    have correct := setCorrect (requestGroupSlot capacity request).1
      (requestGroupSlot capacity request).2
    rw [show paddedTargets (requestGroupSlot capacity request).1
        (requestGroupSlot capacity request).2 = targets request by
      exact paddedGroupedTargets_at_request capacity targets dummy request]
      at correct
    exact correct
  · intro left right sameGroup requestsDifferent
    unfold requestScheduledLineSet
    have localDifferent :
        (requestGroupSlot capacity left).2 ≠
          (requestGroupSlot capacity right).2 := by
      intro sameLocal
      apply requestsDifferent
      have pairEqual : requestGroupSlot capacity left =
          requestGroupSlot capacity right :=
        Prod.ext sameGroup sameLocal
      have flatEqual := congrArg finProdFinEquiv pairEqual
      unfold requestGroupSlot at flatEqual
      simp only [Equiv.apply_symm_apply] at flatEqual
      apply Fin.ext
      exact congrArg
        (fun index : Fin (groups * groupSize) => index.val) flatEqual
    rw [sameGroup]
    exact (pairwise (requestGroupSlot capacity right).1).disjoint_of_ne
      localDifferent

end GroupedScheduler
end MassProduction
end Algebraic
