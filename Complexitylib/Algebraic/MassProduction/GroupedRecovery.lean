/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.GroupedScheduler
public import Complexitylib.Algebraic.MassProduction.ScheduledRecovery

/-!
# Recovery from padded request groups

This module combines arbitrary-count request grouping with the generic
punctured-line recovery interface.  The resource may depend on the request;
this is essential because different mass-production requests carry different
suffix inputs while querying the same family of shorter resource functions.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace GroupedRecovery

open scoped BigOperators LinearAlgebra.Projectivization
open GroupedScheduler
open LineEnumeration
open SchedulerIteration

/-- A pointwise affine-line formula makes the scalar-indexed points for one
real request injective. -/
theorem requestScheduledLinePoint_injective_of_formula
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
    (request : Fin totalRequests) :
    Function.Injective
      (requestScheduledLinePoint widthPositive capacity output request) := by
  intro left right equalPoints
  rw [pointFormula request left, pointFormula request right] at equalPoints
  have equalMultiples :
      enumeratedNonzeroScalar left •
          normalizeBinaryExtensionVector (directions request).rep =
        enumeratedNonzeroScalar right •
          normalizeBinaryExtensionVector (directions request).rep :=
    add_left_cancel equalPoints
  have normalizedNonzero :
      normalizeBinaryExtensionVector (directions request).rep ≠ 0 :=
    normalizeBinaryExtensionVector_ne_zero (directions request).rep
      (directions request).rep_nonzero
  apply enumeratedNonzeroScalar_injective
  exact (smul_left_injective (BinaryExtension width) normalizedNonzero)
    equalMultiples

/-- The scalar-indexed request output and its decoded finite set carry the
same resource sum. -/
theorem sum_requestScheduledLinePoint_eq_set
    {valueType : Type*}
    [AddCommMonoid valueType]
    (widthPositive : 0 < width)
    (capacity : totalRequests <= groups * requestsPerGroup)
    (output : Fin (groups *
      (requestsPerGroup * lineBitWidth dimension width)) -> Bool)
    (resource : (Fin dimension -> BinaryExtension width) -> valueType)
    (request : Fin totalRequests)
    (injective : Function.Injective
      (requestScheduledLinePoint widthPositive capacity output request)) :
    (∑ scalar, resource
        (requestScheduledLinePoint widthPositive capacity output
          request scalar)) =
      ∑ point ∈ requestScheduledLineSet widthPositive capacity output request,
        resource point := by
  unfold requestScheduledLinePoint requestScheduledLineSet
  exact ScheduledRecovery.sum_scheduledLinePoint_eq_sum_scheduledLineSet
    widthPositive _ resource (requestGroupSlot capacity request).2 injective

/-- Exact recovery for arbitrary request counts split among positive groups.
Only requests assigned to the same group are required to have disjoint
recovery sets; every request may carry its own resource evaluation function. -/
theorem paddedGroupedScheduleCircuit_recovers
    {valueType : Type*}
    [AddCommMonoid valueType]
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (groupsPositive : 0 < groups)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= Sorting.networkRecords depth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width)
    (dummy : Fin dimension -> BinaryExtension width)
    (resource : Fin totalRequests ->
      (Fin dimension -> BinaryExtension width) -> valueType)
    (lineRecovery : forall request direction,
      resource request (targets request) =
        ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
          (targets request) direction, resource request point) :
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
            (requestScheduledLineSet widthPositive capacity output right)) /\
      (forall request,
        (∑ scalar, resource request
          (requestScheduledLinePoint widthPositive capacity output
            request scalar)) =
          resource request (targets request)) := by
  dsimp only
  obtain ⟨directions, pointFormula, setFormula, withinGroupDisjoint⟩ :=
    paddedGroupedScheduleCircuit_correct widthPositive widthAtLeastTwo
      groupsPositive allFit directionCapacity targets dummy
  refine ⟨directions, pointFormula, setFormula, withinGroupDisjoint, ?_⟩
  intro request
  calc
    (∑ scalar, resource request
        (requestScheduledLinePoint widthPositive
          (requestGroupCapacity groupsPositive)
          (groupedScheduleOutput dimension widthPositive depth groups
            (requestGroupSize totalRequests groups) allFit
            (paddedGroupedTargets (requestGroupCapacity groupsPositive)
              targets dummy)) request scalar)) =
        ∑ point ∈ requestScheduledLineSet widthPositive
          (requestGroupCapacity groupsPositive)
          (groupedScheduleOutput dimension widthPositive depth groups
            (requestGroupSize totalRequests groups) allFit
            (paddedGroupedTargets (requestGroupCapacity groupsPositive)
              targets dummy)) request,
          resource request point :=
      sum_requestScheduledLinePoint_eq_set widthPositive _ _
        (resource request) request
        (requestScheduledLinePoint_injective_of_formula widthPositive _ _
          targets directions pointFormula request)
    _ = ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
          (targets request) (directions request), resource request point := by
      rw [setFormula request]
    _ = resource request (targets request) :=
      (lineRecovery request (directions request)).symm

end GroupedRecovery
end MassProduction
end Algebraic
