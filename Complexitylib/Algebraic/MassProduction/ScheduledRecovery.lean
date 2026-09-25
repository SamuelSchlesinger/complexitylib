/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Recovery
public import Complexitylib.Algebraic.MassProduction.SchedulerIteration

/-!
# Recovery from the constructive schedule

This module connects the explicit unrolled scheduler circuit to the abstract
local-recovery identity.  It proves that summing a resource over the actual
request-major point records emitted by the circuit recovers every requested
target value.

The resource codomain is kept abstract.  In particular, this layer needs no
new global finite-field or decidable-equality instances; classical equality
is introduced only inside the finite-sum proof.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace ScheduledRecovery

open scoped BigOperators LinearAlgebra.Projectivization
open LineEnumeration
open SchedulerIteration

/-- Under the scheduler's pointwise line formula, different scalar positions
decode to different emitted points. -/
theorem scheduledLinePoint_injective_of_formula
    (widthPositive : 0 < width)
    (output : Fin (requests * lineBitWidth dimension width) -> Bool)
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width)
    (directions : Fin requests ->
      ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))
    (pointFormula : ∀ request scalar,
      scheduledLinePoint widthPositive output request scalar =
        targets request + enumeratedNonzeroScalar scalar •
          normalizeBinaryExtensionVector (directions request).rep)
    (request : Fin requests) :
    Function.Injective
      (scheduledLinePoint widthPositive output request) := by
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

/-- Summing over the scalar-indexed output records is the same as summing
over the decoded finite recovery set, provided those records are distinct. -/
theorem sum_scheduledLinePoint_eq_sum_scheduledLineSet
    {valueType : Type*}
    [AddCommMonoid valueType]
    (widthPositive : 0 < width)
    (output : Fin (requests * lineBitWidth dimension width) -> Bool)
    (resource : (Fin dimension -> BinaryExtension width) -> valueType)
    (request : Fin requests)
    (injective : Function.Injective
      (scheduledLinePoint widthPositive output request)) :
    ∑ scalar, resource
        (scheduledLinePoint widthPositive output request scalar) =
      ∑ point ∈ scheduledLineSet widthPositive output request,
        resource point := by
  classical
  unfold scheduledLineSet decodedLineOutputSet scheduledLinePoint
  rw [Finset.sum_image]
  exact injective.injOn

/-- Exact recovery theorem for the concrete greedy scheduler circuit.  Any
resource family satisfying the punctured-line identity recovers all targets
when read in the circuit's emitted request/scalar order. -/
theorem greedyScheduleCircuit_recovers
    {valueType : Type*}
    [AddCommMonoid valueType]
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (requests : Nat)
    (allFit : requests * nonzeroScalarCount width ≤
      Sorting.networkRecords depth)
    (capacity : requests * nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width)
    (resource : (Fin dimension -> BinaryExtension width) -> valueType)
    (lineRecovery : ∀ target direction,
      resource target =
        ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
          target direction, resource point) :
    ∃ directions : Fin requests ->
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width),
      (∀ request scalar,
        scheduledLinePoint widthPositive
            (greedyScheduleOutput dimension widthPositive depth requests
              allFit targets) request scalar =
          targets request + enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector (directions request).rep) ∧
      (∀ request,
        scheduledLineSet widthPositive
            (greedyScheduleOutput dimension widthPositive depth requests
              allFit targets) request =
          ForbiddenRanks.binaryExtensionPuncturedLine
            (targets request) (directions request)) ∧
      PairwiseDisjointFamily
        (scheduledLineSet widthPositive
          (greedyScheduleOutput dimension widthPositive depth requests
            allFit targets)) ∧
      ∀ request,
        (∑ scalar, resource
          (scheduledLinePoint widthPositive
            (greedyScheduleOutput dimension widthPositive depth requests
              allFit targets) request scalar)) =
          resource (targets request) := by
  classical
  obtain ⟨directions, pointFormula, setFormula, pairwise⟩ :=
    greedyScheduleCircuit_correct widthPositive widthAtLeastTwo requests
      allFit capacity targets
  refine ⟨directions, pointFormula, setFormula, pairwise, ?_⟩
  intro request
  calc
    (∑ scalar, resource
        (scheduledLinePoint widthPositive
          (greedyScheduleOutput dimension widthPositive depth requests
            allFit targets) request scalar)) =
        ∑ point ∈ scheduledLineSet widthPositive
          (greedyScheduleOutput dimension widthPositive depth requests
            allFit targets) request, resource point :=
      sum_scheduledLinePoint_eq_sum_scheduledLineSet widthPositive _
        resource request
        (scheduledLinePoint_injective_of_formula widthPositive _ targets
          directions pointFormula request)
    _ = ∑ point ∈ ForbiddenRanks.binaryExtensionPuncturedLine
          (targets request) (directions request), resource point := by
      rw [setFormula request]
    _ = resource (targets request) :=
      (lineRecovery (targets request) (directions request)).symm

end ScheduledRecovery
end MassProduction
end Algebraic
