/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CompositionBound
public import Mathlib.Data.Nat.Log

/-!
# Canonical finite parameters for mass-production composition

The raw composition theorem exposes every routing width, sorting-network
depth, and padding count.  This module chooses each of those bookkeeping
parameters canonically by ceiling binary logarithms.  The only hypotheses
left to later asymptotic work are the mathematical ones: packing into the
evaluation-code grid and availability of enough projective directions.

No instances are declared here.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace FiniteParameters

open scoped LinearAlgebra.Projectivization
open CanonicalPacking
open GroupedScheduler
open IncidenceRouting
open LineEnumeration
open ResourceEvaluation
open Sorting

/-- Depth of the least power-of-two layout large enough for `records`. -/
def binaryDepth (records : Nat) : Nat :=
  Nat.clog 2 records

theorem records_le_networkRecords (records : Nat) :
    records <= networkRecords (binaryDepth records) := by
  rw [networkRecords_eq_two_pow]
  exact Nat.le_pow_clog (by omega) records

/-- Canonical padding from a live prefix to the next power-of-two layout. -/
def paddingCount (records : Nat) : Nat :=
  networkRecords (binaryDepth records) - records

theorem records_add_paddingCount (records : Nat) :
    records + paddingCount records = networkRecords (binaryDepth records) := by
  unfold paddingCount
  exact Nat.add_sub_of_le (records_le_networkRecords records)

/-- The least power-of-two layout wastes less than a factor of two when the
live record count is positive. -/
theorem networkRecords_binaryDepth_lt_two_mul
    (records : Nat) (recordsPositive : 0 < records) :
    networkRecords (binaryDepth records) < 2 * records := by
  rw [networkRecords_eq_two_pow]
  unfold binaryDepth
  by_cases recordsOne : records = 1
  · subst records
    norm_num [Nat.clog]
  · have recordsAtLeastTwo : 1 < records := by omega
    have predecessorBound := Nat.pow_pred_clog_lt_self
      (b := 2) (by omega) recordsAtLeastTwo
    have clogPositive : 0 < Nat.clog 2 records := by
      rw [Nat.lt_clog_iff_pow_lt (by omega)]
      simpa using recordsAtLeastTwo
    calc
      2 ^ Nat.clog 2 records =
          2 * 2 ^ (Nat.clog 2 records - 1) := by
        conv_lhs =>
          rw [show Nat.clog 2 records =
            (Nat.clog 2 records - 1) + 1 by omega]
        rw [Nat.pow_succ]
        ring
      _ < 2 * records := Nat.mul_lt_mul_of_pos_left predecessorBound (by omega)

theorem binaryDepth_le
    (records bound : Nat)
    (fits : records <= 2 ^ bound) :
    binaryDepth records <= bound := by
  unfold binaryDepth
  exact Nat.clog_le_of_le_pow fits

/-- Bit width used for a group index. -/
def groupBitWidth (groups : Nat) : Nat :=
  binaryDepth groups

theorem groups_fit (groups : Nat) :
    groups <= 2 ^ groupBitWidth groups := by
  simpa only [groupBitWidth, binaryDepth] using
    Nat.le_pow_clog (by omega : 1 < 2) groups

/-- Number of scheduled non-target incidences. -/
noncomputable def incidenceCount (totalRequests width : Nat) : Nat :=
  totalRequests * nonzeroScalarCount width

/-- Sorting depth sufficient for one group's greedy scheduler state. -/
noncomputable def schedulerDepth
    (totalRequests groups width : Nat) : Nat :=
  binaryDepth (requestGroupSize totalRequests groups *
    nonzeroScalarCount width)

theorem scheduler_fits (totalRequests groups width : Nat) :
    requestGroupSize totalRequests groups * nonzeroScalarCount width <=
      networkRecords (schedulerDepth totalRequests groups width) := by
  exact records_le_networkRecords _

/-- Bit width sufficient to retain the original incidence order. -/
noncomputable def orderWidth (totalRequests width : Nat) : Nat :=
  binaryDepth (incidenceCount totalRequests width)

theorem incidences_fit (totalRequests width : Nat) :
    incidenceCount totalRequests width <=
      2 ^ orderWidth totalRequests width := by
  simpa only [orderWidth, binaryDepth] using
    Nat.le_pow_clog (by omega : 1 < 2)
      (incidenceCount totalRequests width)

/-- Number of canonical `(group, affine point)` resource slots. -/
def resourceSlotCount
    (groups dimension width : Nat) : Nat :=
  2 ^ (groupBitWidth groups + dimension * width)

/-- Live record count shared by scatter and gather. -/
noncomputable def routingRecords
    (totalRequests groups dimension width : Nat) : Nat :=
  incidenceCount totalRequests width +
    resourceSlotCount groups dimension width

/-- Common power-of-two sorting depth for scatter and gather. -/
noncomputable def routingDepth
    (totalRequests groups dimension width : Nat) : Nat :=
  binaryDepth (routingRecords totalRequests groups dimension width)

/-- Padding count for either routing pass. -/
noncomputable def routingPadding
    (totalRequests groups dimension width : Nat) : Nat :=
  paddingCount (routingRecords totalRequests groups dimension width)

theorem scatter_record_count
    (totalRequests groups dimension width : Nat) :
    incidenceCount totalRequests width +
        resourceSlotCount groups dimension width +
        routingPadding totalRequests groups dimension width =
      networkRecords (routingDepth totalRequests groups dimension width) := by
  exact records_add_paddingCount _

theorem gather_record_count
    (totalRequests groups dimension width : Nat) :
    resourceSlotCount groups dimension width +
        incidenceCount totalRequests width +
        routingPadding totalRequests groups dimension width =
      networkRecords (routingDepth totalRequests groups dimension width) := by
  rw [Nat.add_comm (resourceSlotCount groups dimension width)]
  exact scatter_record_count totalRequests groups dimension width

/-- The fully instantiated finite bound. -/
@[reducible] noncomputable def canonicalCostBound
    (totalRequests groups prefixWidth dimension width suffixWidth
      resourceBound : Nat) : Nat :=
  CompositionBound.costBound totalRequests groups prefixWidth dimension width
    suffixWidth (schedulerDepth totalRequests groups width)
    (groupBitWidth groups) (orderWidth totalRequests width)
    (routingDepth totalRequests groups dimension width)
    (routingDepth totalRequests groups dimension width) resourceBound

set_option maxHeartbeats 3000000 in
/-- Canonically parameterized complexity-only composition theorem. -/
theorem booleanMassComplexity_le
    (totalRequests groups prefixWidth dimension width suffixWidth : Nat)
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (dimensionPositive : 0 < dimension)
    (gridPositive : 0 < gridWidth dimension width)
    (groupsPositive : 0 < groups)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (suffixLarge : 16 <= suffixWidth)
    (directionCapacity : requestGroupSize totalRequests groups *
        nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (function :
      Fin (2 ^ prefixWidth) -> (Fin suffixWidth -> Bool) -> Bool)
    (resourceBound : Nat)
    (resourceComplexity : forall member,
      booleanMassComplexity
          (CompositionBound.canonicalResourceFunction widthPositive
            packingFits function member)
          groups <= (resourceBound : Nat)) :
    booleanMassComplexity (RuntimePipeline.requestFunction function)
        totalRequests <=
      (canonicalCostBound totalRequests groups prefixWidth dimension width
        suffixWidth resourceBound : Nat) := by
  apply CompositionBound.booleanMassComplexity_le_of_resource_complexity
    widthPositive widthAtLeastTwo dimensionPositive gridPositive
    groupsPositive packingFits
    (schedulerDepth totalRequests groups width) suffixWidth
    (groupBitWidth groups) (orderWidth totalRequests width) suffixLarge
    (groups_fit groups) (scheduler_fits totalRequests groups width)
    directionCapacity
    (show totalRequests * nonzeroScalarCount width <=
        2 ^ orderWidth totalRequests width from
      incidences_fit totalRequests width)
    function (fun _ => 0)
    (scatterPaddingCount :=
      routingPadding totalRequests groups dimension width)
    (scatter_record_count totalRequests groups dimension width)
    resourceBound resourceComplexity
    (gatherPaddingCount :=
      routingPadding totalRequests groups dimension width)
    (gather_record_count totalRequests groups dimension width)

end FiniteParameters
end MassProduction
end Algebraic
