/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.GroupedRecovery
public import Complexitylib.Algebraic.MassProduction.ResourcePacking

/-!
# Grouped recovery of packed Boolean requests

This is the semantic junction between the manuscript's packing, geometric
scheduler, and bounded-demand grouping.  Each request supplies a source
information coordinate and a suffix.  The grouped scheduler emits a
punctured line, and the indicated bit of the field-resource sum is proved to
be the original Boolean function value for that request.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

universe u

variable {Prefix : Type u}
namespace PackedGroupedRecovery

open scoped BigOperators LinearAlgebra.Projectivization
open GroupedRecovery
open GroupedScheduler
open LineEnumeration

/-- The complete packed, grouped, scheduled recovery invariant. -/
theorem packedGroupedSchedule_recovers
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (groupsPositive : 0 < groups)
    (allFit : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <= Sorting.networkRecords depth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> Suffix -> Bool)
    (requestSource : Fin totalRequests -> Prefix)
    (requestSuffix : Fin totalRequests -> Suffix)
    (dummy : Fin dimension -> BinaryExtension width) :
    let targets : Fin totalRequests ->
        Fin dimension -> BinaryExtension width :=
      fun request => packedTargetPoint widthPositive placement
        (requestSource request)
    let groupSize := requestGroupSize totalRequests groups
    let capacity := requestGroupCapacity
      (totalRequests := totalRequests) groupsPositive
    let paddedTargets := paddedGroupedTargets capacity targets dummy
    let output := groupedScheduleOutput dimension widthPositive depth groups
      groupSize allFit paddedTargets
    exists directions : Fin totalRequests ->
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width),
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
        (∑ scalar,
          decodeBinaryExtension widthPositive
            (packedEvaluationResource widthPositive placement function
              (requestScheduledLinePoint widthPositive capacity output
                request scalar)
              (requestSuffix request))
            (placement (requestSource request)).2) =
          function (requestSource request) (requestSuffix request)) := by
  dsimp only
  let targets : Fin totalRequests ->
      Fin dimension -> BinaryExtension width :=
    fun request => packedTargetPoint widthPositive placement
      (requestSource request)
  let capacity := requestGroupCapacity
    (totalRequests := totalRequests) groupsPositive
  let paddedTargets := paddedGroupedTargets capacity targets dummy
  let output := groupedScheduleOutput dimension widthPositive depth groups
    (requestGroupSize totalRequests groups) allFit paddedTargets
  let resource : Fin totalRequests ->
      (Fin dimension -> BinaryExtension width) -> Bool :=
    fun request point =>
      decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function point
          (requestSuffix request))
        (placement (requestSource request)).2
  have lineRecovery : forall request direction,
      resource request (targets request) =
        ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
          (targets request) direction, resource request point := by
    intro request direction
    have targetValue := packedEvaluationResource_at_target widthPositive
      placement function (requestSource request) (requestSuffix request)
    have lineValue := packedEvaluationResource_sum_puncturedLine
      widthPositive dimensionPositive placement function
      (requestSource request) (requestSuffix request) direction
    change resource request (targets request) =
      ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
        (targets request) direction, resource request point
    change resource request (targets request) =
      function (requestSource request) (requestSuffix request) at targetValue
    change (∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
        (targets request) direction, resource request point) =
      function (requestSource request) (requestSuffix request) at lineValue
    exact targetValue.trans lineValue.symm
  obtain ⟨directions, _pointFormula, setFormula, withinGroupDisjoint,
      resourceRecovery⟩ :=
    paddedGroupedScheduleCircuit_recovers widthPositive widthAtLeastTwo
      groupsPositive allFit directionCapacity targets dummy resource
      lineRecovery
  refine ⟨directions, setFormula, withinGroupDisjoint, ?_⟩
  intro request
  have recovered := resourceRecovery request
  have targetValue := packedEvaluationResource_at_target widthPositive
    placement function (requestSource request) (requestSuffix request)
  change (∑ scalar, resource request
      (requestScheduledLinePoint widthPositive capacity output
        request scalar)) =
    function (requestSource request) (requestSuffix request)
  exact recovered.trans targetValue

end PackedGroupedRecovery
end MassProduction
end Algebraic
