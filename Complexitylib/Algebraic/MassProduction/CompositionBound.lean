/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.RuntimePipeline
public import Complexitylib.Algebraic.MassProduction.ShannonSynthesis
public import Complexitylib.Algebraic.MassProduction.Statement

/-!
# Finite composition bound

This module packages the exact runtime pipeline as the finite counterpart of
the manuscript's composition proposition.  If every shorter resource circuit
has cost at most `resourceBound`, then the resource term is

`resourceBitCount dimension width * resourceBound`,

the literal `q^ell * b * L_C(d)` term.  Every remaining contribution is an
explicit natural-number expression.  No asymptotic notation and no new
type-class instances are used here.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace CompositionBound

open scoped LinearAlgebra.Projectivization
open CanonicalPacking
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open ResourceEvaluation
open RoutingAssembly
open RuntimePipeline
open SchedulerIteration
open Sorting

/-- Explicit upper bound for runtime canonical prefix packing per request. -/
@[reducible] noncomputable def packingCostBound
    (prefixWidth dimension width : Nat) : Nat :=
  prefixWidth * (8 * width) +
    dimension * (prefixWidth * (8 * gridWidth dimension width)) +
    dimension * width * (2 * gridWidth dimension width)

/-- The polynomial bound proved for the two-sort scatter router. -/
@[reducible] def scatterRoutingCostBound
    (depth keyWidth payloadWidth : Nat) : Nat :=
  (depth * depth * networkRecords depth *
      ((2 * Routing.recordWidth keyWidth payloadWidth) *
        (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
    networkBits depth (Routing.recordWidth keyWidth payloadWidth) *
      (12 * keyWidth + 12)) +
  (networkBits depth (Routing.recordWidth keyWidth payloadWidth) +
    depth * depth * networkRecords depth *
      ((2 * Routing.recordWidth keyWidth payloadWidth) *
        (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)))

/-- The polynomial bound proved for the metadata-preserving gather router. -/
@[reducible] def gatherRoutingCostBound
    (depth keyWidth metadataWidth valueWidth : Nat) : Nat :=
  (depth * depth * networkRecords depth *
      ((2 * RoutingMetadata.recordWidth keyWidth metadataWidth valueWidth) *
        (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
    networkBits depth
        (RoutingMetadata.recordWidth keyWidth metadataWidth valueWidth) *
      (12 * keyWidth + 12)) +
  (networkBits depth
      (RoutingMetadata.recordWidth keyWidth metadataWidth valueWidth) +
    depth * depth * networkRecords depth *
      ((2 * RoutingMetadata.recordWidth
          keyWidth metadataWidth valueWidth) *
        (2 * ((metadataWidth + 1) *
          (6 * (metadataWidth + 1) + 4)) + 4)))

/-- Every non-resource contribution in the concrete finite construction. -/
@[reducible] noncomputable def overheadCostBound
    (totalRequests groups prefixWidth dimension width suffixWidth
      schedulerDepth groupBitWidth orderWidth scatterDepth gatherDepth : Nat) :
    Nat :=
  groups * requestGroupSize totalRequests groups *
      scheduledLineEnumerationCostBound dimension width schedulerDepth +
    totalRequests * packingCostBound prefixWidth dimension width +
    scatterRoutingCostBound scatterDepth
      (incidenceKeyWidth groupBitWidth dimension width) suffixWidth +
    gatherRoutingCostBound gatherDepth
      (incidenceKeyWidth groupBitWidth dimension width)
      (orderWidth + 1) width +
    totalRequests * (nonzeroScalarCount width * width * 5)

/-- Finite form of the master ledger: resource count times a uniform shorter
resource bound, plus the fully explicit overhead. -/
@[reducible] noncomputable def costBound
    (totalRequests groups prefixWidth dimension width suffixWidth
      schedulerDepth groupBitWidth orderWidth scatterDepth gatherDepth
      resourceBound : Nat) : Nat :=
  resourceBitCount dimension width * resourceBound +
    overheadCostBound totalRequests groups prefixWidth dimension width
      suffixWidth schedulerDepth groupBitWidth orderWidth scatterDepth
      gatherDepth

private theorem sum_resource_cost_le
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (resourceBound : Nat)
    (bounded : forall member,
      (resourceCircuits member).cost DeMorgan.standardCost <= resourceBound) :
    (∑ member, (resourceCircuits member).cost DeMorgan.standardCost) <=
      resourceBitCount dimension width * resourceBound := by
  calc
    (∑ member, (resourceCircuits member).cost DeMorgan.standardCost) <=
        ∑ _member : Fin (resourceBitCount dimension width), resourceBound :=
      Finset.sum_le_sum fun member _membership => bounded member
    _ = resourceBitCount dimension width * resourceBound := by simp

/-- Concrete natural-number composition bound for the runtime circuit. -/
theorem circuit_cost_le
    (widthPositive : 0 < width)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (resourceBound : Nat)
    (resourcesBounded : forall member,
      (resourceCircuits member).cost DeMorgan.standardCost <= resourceBound)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    (RuntimePipeline.circuit (prefixWidth := prefixWidth) widthPositive
      gridPositive groupsPositive schedulerDepth suffixWidth groupBitWidth
      orderWidth allFit incidenceFits dummyTarget scatterRecordCount
       resourceCircuits gatherRecordCount).cost
        DeMorgan.standardCost <=
      costBound totalRequests groups prefixWidth dimension width suffixWidth
        schedulerDepth groupBitWidth orderWidth scatterDepth gatherDepth
        resourceBound := by
  rw [RuntimePipeline.circuit_cost_expanded]
  have schedulerBound := groupedScheduleCircuit_cost_le
    (dimension := dimension) (depth := schedulerDepth) (groups := groups)
    widthPositive allFit
  have packingBound := Nat.mul_le_mul_left totalRequests
    (RuntimePacking.circuit_cost_le
      (prefixWidth := prefixWidth) (dimension := dimension)
      widthPositive gridPositive)
  have scatterBound := CanonicalRouting.matchedCanonicalRoutingCircuit_cost_le
    (depth := scatterDepth)
    (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
    (payloadWidth := suffixWidth)
  have resourcesBound := sum_resource_cost_le resourceCircuits
    resourceBound resourcesBounded
  have gatherBound :=
    CanonicalMetadataRouting.matchedCanonicalRoutingCircuit_cost_le
      (depth := gatherDepth)
      (keyWidth := incidenceKeyWidth groupBitWidth dimension width)
      (metadataWidth := orderWidth + 1) (valueWidth := width)
  unfold costBound overheadCostBound packingCostBound
    scatterRoutingCostBound gatherRoutingCostBound
  omega

set_option maxHeartbeats 2500000 in
/-- Complexity-theoretic form of the finite composition proposition.  The
left side is the minimum circuit cost of the ordinary runtime direct product;
the right side is resource count times the supplied shorter bound plus the
explicit overhead. -/
theorem booleanMassComplexity_le
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceCircuits : Fin (resourceBitCount dimension width) ->
      Circuit DeMorgan.signature (groups * suffixWidth) groups)
    (resourcesCompute : forall
      (point : Fin (pointCount dimension width)) (bit : Fin width),
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction
            (Prefix := Fin (2 ^ prefixWidth))
            (dimension := dimension) (width := width)
            (suffixWidth := suffixWidth) widthPositive
            ((CanonicalPacking.packedPlacement widthPositive packingFits) :
              Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
            function point bit)
          groups))
    (resourceBound : Nat)
    (resourcesBounded : forall member,
      (resourceCircuits member).cost DeMorgan.standardCost <= resourceBound)
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    booleanMassComplexity (RuntimePipeline.requestFunction function)
        totalRequests <=
      (costBound totalRequests groups prefixWidth dimension width suffixWidth
        schedulerDepth groupBitWidth orderWidth scatterDepth gatherDepth
        resourceBound : Nat) := by
  let runtimeCircuit := RuntimePipeline.circuit
    (prefixWidth := prefixWidth) widthPositive gridPositive groupsPositive
    schedulerDepth suffixWidth groupBitWidth orderWidth allFit incidenceFits
    dummyTarget scatterRecordCount resourceCircuits
    gatherRecordCount
  have computesAll : runtimeCircuit.ComputesWith DeMorgan.interpretation
      (directProduct (RuntimePipeline.requestFunction function)
        totalRequests) :=
    RuntimePipeline.circuit_computes widthPositive widthAtLeastTwo
      dimensionPositive gridPositive groupsPositive packingFits
      schedulerDepth suffixWidth groupBitWidth orderWidth groupFits allFit
      directionCapacity incidenceFits function dummyTarget scatterRecordCount
       resourceCircuits resourcesCompute gatherRecordCount
  have upper := runtimeCircuit.costComplexity_le
    DeMorgan.standardCost computesAll
  have finiteCost :
      runtimeCircuit.cost DeMorgan.standardCost <=
        costBound totalRequests groups prefixWidth dimension width suffixWidth
          schedulerDepth groupBitWidth orderWidth scatterDepth gatherDepth
          resourceBound :=
    circuit_cost_le (prefixWidth := prefixWidth) widthPositive gridPositive
      groupsPositive schedulerDepth suffixWidth groupBitWidth orderWidth allFit
      incidenceFits dummyTarget scatterRecordCount resourceCircuits
      resourceBound resourcesBounded gatherRecordCount
  have castCost :
      (runtimeCircuit.cost DeMorgan.standardCost : ENat) <=
        (costBound totalRequests groups prefixWidth dimension width suffixWidth
          schedulerDepth groupBitWidth orderWidth scatterDepth gatherDepth
          resourceBound : Nat) := by
    exact_mod_cast finiteCost
  unfold booleanMassComplexity
  exact upper.trans castCost

/-- Canonically indexed shorter resource function used by the runtime
composition. -/
noncomputable def canonicalResourceFunction
    (widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (member : Fin (resourceBitCount dimension width)) :
    ScalarFunction Bool suffixWidth :=
  packedResourceFunction widthPositive
    ((CanonicalPacking.packedPlacement widthPositive packingFits) :
      Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
    function (resourceMemberAt member).1 (resourceMemberAt member).2

@[simp] theorem canonicalResourceFunction_index
    (widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (point : Fin (pointCount dimension width))
    (bit : Fin width) :
    canonicalResourceFunction widthPositive packingFits function
        (resourceMemberIndex point bit) =
      packedResourceFunction widthPositive
        ((CanonicalPacking.packedPlacement widthPositive packingFits) :
          Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
        function point bit := by
  simp [canonicalResourceFunction]

set_option maxHeartbeats 3000000 in
/-- Complexity-only interface to the finite composition theorem.  Shannon
replication witnesses that every shorter direct product is realizable; a
minimum circuit is then selected for each resource.  Consequently callers
only need to supply a uniform complexity bound, rather than a dependent
family of concrete circuits. -/
theorem booleanMassComplexity_le_of_resource_complexity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (schedulerDepth suffixWidth groupBitWidth orderWidth : Nat)
    (suffixLarge : 16 <= suffixWidth)
    (groupFits : groups <= 2 ^ groupBitWidth)
    (allFit : requestGroupSize totalRequests groups *
      nonzeroScalarCount width <= networkRecords schedulerDepth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (incidenceFits :
      totalRequests * nonzeroScalarCount width <= 2 ^ orderWidth)
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (dummyTarget : Fin dimension -> BinaryExtension width)
    (scatterRecordCount :
      totalRequests * nonzeroScalarCount width +
          2 ^ (groupBitWidth + dimension * width) + scatterPaddingCount =
        networkRecords scatterDepth)
    (resourceBound : Nat)
    (resourceComplexity : forall member,
      booleanMassComplexity
          (canonicalResourceFunction widthPositive packingFits function member)
          groups <= (resourceBound : Nat))
    (gatherRecordCount :
      2 ^ (groupBitWidth + dimension * width) +
          totalRequests * nonzeroScalarCount width + gatherPaddingCount =
        networkRecords gatherDepth) :
    booleanMassComplexity (RuntimePipeline.requestFunction function)
        totalRequests <=
      (costBound totalRequests groups prefixWidth dimension width suffixWidth
        schedulerDepth groupBitWidth orderWidth scatterDepth gatherDepth
        resourceBound : Nat) := by
  let resourceMinimum := fun member :
      Fin (resourceBitCount dimension width) =>
    ShannonSynthesis.minimumMassCircuit suffixWidth suffixLarge
      (canonicalResourceFunction widthPositive packingFits function member)
      groups
  let resourceCircuits := fun member :
      Fin (resourceBitCount dimension width) =>
    (resourceMinimum member).circuit
  have resourcesCompute : forall
      (point : Fin (pointCount dimension width)) (bit : Fin width),
      (resourceCircuits (resourceMemberIndex point bit)).ComputesWith
        DeMorgan.interpretation
        (directProduct
          (packedResourceFunction
            (Prefix := Fin (2 ^ prefixWidth))
            (dimension := dimension) (width := width)
            (suffixWidth := suffixWidth) widthPositive
            ((CanonicalPacking.packedPlacement widthPositive packingFits) :
              Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width)
            function point bit)
          groups) := by
    intro point bit
    change (resourceMinimum (resourceMemberIndex point bit)).circuit.ComputesWith
      DeMorgan.interpretation _
    simpa only [canonicalResourceFunction_index] using
      (resourceMinimum (resourceMemberIndex point bit)).computes
  have resourcesBounded : forall member,
      (resourceCircuits member).cost DeMorgan.standardCost <= resourceBound := by
    intro member
    exact ShannonSynthesis.minimumMassCircuit_cost_le suffixWidth suffixLarge
      (canonicalResourceFunction widthPositive packingFits function member)
      groups resourceBound (resourceComplexity member)
  exact booleanMassComplexity_le widthPositive widthAtLeastTwo
    dimensionPositive gridPositive groupsPositive packingFits schedulerDepth
    suffixWidth groupBitWidth orderWidth groupFits allFit directionCapacity
    incidenceFits function dummyTarget scatterRecordCount
    resourceCircuits resourcesCompute resourceBound resourcesBounded
    gatherRecordCount

end CompositionBound
end MassProduction
end Algebraic
