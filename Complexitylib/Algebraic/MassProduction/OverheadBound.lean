/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CodeParameters

/-!
# Factored polynomial overhead bound

The concrete composition ledger contains several large expanded formulas.
This module factors each of them into the number of live power-of-two records
times a polynomial coefficient in bit widths and sorting depths.  The result
retains the manuscript's three meaningful volumes: grouped scheduler work,
incidences, and resource slots.  No asymptotic notation and no instances are
introduced.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace OverheadBound

open CanonicalPacking
open CompositionBound
open GroupedScheduler
open LeastMissing
open LineEnumeration
open Routing
open RoutingMetadata
open Sorting

/-- Non-record-multiplied cost of projective unranking in one scheduler
stage. -/
def schedulerStandaloneCoefficient (dimension width : Nat) : Nat :=
  (dimension * width) *
    (dimension *
      (2 * width + 2 + dimension * (2 * width + 1) + 2))

/-- Coefficient of `networkRecords depth` in fresh-rank selection. -/
def freshRankRecordedCoefficient
    (dimension width depth : Nat) : Nat :=
  depth * depth *
      ((2 * (dimension * width)) *
        (2 * ((dimension * width) *
          (6 * (dimension * width) + 4)) + 4)) +
    ((candidateRecordWidth (dimension * width)) *
        candidateOutputCostBound (dimension * width) +
      depth * depth *
        ((2 * candidateRecordWidth (dimension * width)) *
          (2 * (1 * (6 * 1 + 4)) + 4)))

/-- Complete coefficient of record-multiplied work in one scheduler stage. -/
def schedulerRecordedCoefficient
    (dimension width depth : Nat) : Nat :=
  dimension * (4 * width) +
    ForbiddenRanks.guardedProjectiveRankCostBound dimension width +
    freshRankRecordedCoefficient dimension width depth

/-- Polynomial coefficient which absorbs both record-multiplied and the
standalone work of one scheduler stage. -/
def schedulerCoefficient (dimension width depth : Nat) : Nat :=
  schedulerRecordedCoefficient dimension width depth +
    schedulerStandaloneCoefficient dimension width

/-- Per-field-element polynomial work of explicit line enumeration. -/
def lineCoefficient (dimension width : Nat) : Nat :=
  dimension * (width * (6 * (width * width)) + 4 * width)

theorem schedulerStageCostBound_eq
    (dimension width depth : Nat) :
    SchedulerStage.schedulerStageCostBound dimension width depth =
      networkRecords depth *
          schedulerRecordedCoefficient dimension width depth +
        schedulerStandaloneCoefficient dimension width := by
  unfold SchedulerStage.schedulerStageCostBound
    ForbiddenRanks.freshDirectionFromDifferencesCostBound
    ForbiddenRanks.forbiddenRankArrayCostBound
    FreshDirection.freshProjectiveDirectionCostBound
    FreshDirection.freshProjectiveRankCostBound
    schedulerRecordedCoefficient freshRankRecordedCoefficient
    schedulerStandaloneCoefficient
  simp only [networkBits, candidateRecordWidth]
  ring

theorem schedulerStageCostBound_le
    (dimension width depth : Nat) :
    SchedulerStage.schedulerStageCostBound dimension width depth <=
      networkRecords depth * schedulerCoefficient dimension width depth := by
  rw [schedulerStageCostBound_eq]
  unfold schedulerCoefficient
  have recordsPositive : 1 <= networkRecords depth := by
    rw [networkRecords_eq_two_pow]
    exact Nat.one_le_pow depth 2 (by omega)
  have standaloneBound : schedulerStandaloneCoefficient dimension width <=
      networkRecords depth * schedulerStandaloneCoefficient dimension width := by
    nth_rewrite 1 [← Nat.one_mul
      (schedulerStandaloneCoefficient dimension width)]
    exact Nat.mul_le_mul_right _ recordsPositive
  calc
    networkRecords depth * schedulerRecordedCoefficient dimension width depth +
        schedulerStandaloneCoefficient dimension width <=
      networkRecords depth * schedulerRecordedCoefficient dimension width depth +
        networkRecords depth * schedulerStandaloneCoefficient dimension width :=
      Nat.add_le_add_left standaloneBound _
    _ = networkRecords depth *
        (schedulerRecordedCoefficient dimension width depth +
          schedulerStandaloneCoefficient dimension width) := by ring

theorem scheduledLineEnumerationCostBound_le
    (dimension width depth : Nat) :
    scheduledLineEnumerationCostBound dimension width depth <=
      networkRecords depth * schedulerCoefficient dimension width depth +
        2 ^ width * lineCoefficient dimension width := by
  unfold scheduledLineEnumerationCostBound lineCoefficient
  apply Nat.add_le_add
  · exact schedulerStageCostBound_le dimension width depth
  · apply Nat.mul_le_mul_right
    exact Nat.sub_le _ _

/-- Polynomial multiplier after factoring out the scatter record count. -/
def scatterCoefficient (depth keyWidth payloadWidth : Nat) : Nat :=
  depth * depth *
      ((2 * Routing.recordWidth keyWidth payloadWidth) *
        (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
    Routing.recordWidth keyWidth payloadWidth * (12 * keyWidth + 12) +
    Routing.recordWidth keyWidth payloadWidth +
    depth * depth *
      ((2 * Routing.recordWidth keyWidth payloadWidth) *
        (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4))

theorem scatterRoutingCostBound_eq
    (depth keyWidth payloadWidth : Nat) :
    scatterRoutingCostBound depth keyWidth payloadWidth =
      networkRecords depth *
        scatterCoefficient depth keyWidth payloadWidth := by
  unfold scatterRoutingCostBound scatterCoefficient networkBits
  ring

/-- Polynomial multiplier after factoring out the gather record count. -/
def gatherCoefficient
    (depth keyWidth metadataWidth valueWidth : Nat) : Nat :=
  depth * depth *
      ((2 * RoutingMetadata.recordWidth keyWidth metadataWidth valueWidth) *
        (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
    RoutingMetadata.recordWidth keyWidth metadataWidth valueWidth *
      (12 * keyWidth + 12) +
    RoutingMetadata.recordWidth keyWidth metadataWidth valueWidth +
    depth * depth *
      ((2 * RoutingMetadata.recordWidth
          keyWidth metadataWidth valueWidth) *
        (2 * ((metadataWidth + 1) *
          (6 * (metadataWidth + 1) + 4)) + 4))

theorem gatherRoutingCostBound_eq
    (depth keyWidth metadataWidth valueWidth : Nat) :
    gatherRoutingCostBound depth keyWidth metadataWidth valueWidth =
      networkRecords depth *
        gatherCoefficient depth keyWidth metadataWidth valueWidth := by
  unfold gatherRoutingCostBound gatherCoefficient networkBits
  ring

/-- Polynomial multiplier for runtime prefix packing after factoring out one
field cardinality. -/
def packingCoefficient
    (prefixWidth dimension width : Nat) : Nat :=
  prefixWidth * (8 * width) +
    dimension * (prefixWidth * 8) +
    dimension * width * 2

theorem gridWidth_le_fieldCard
    (dimension width : Nat)
    (widthPositive : 0 < width) :
    gridWidth dimension width <= 2 ^ width := by
  rw [gridWidth_eq widthPositive]
  unfold resourceGridWidth
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem packingCostBound_le
    (prefixWidth dimension width : Nat)
    (widthPositive : 0 < width) :
    packingCostBound prefixWidth dimension width <=
      2 ^ width * packingCoefficient prefixWidth dimension width := by
  let fieldCard := 2 ^ width
  have fieldCardPositive : 1 <= fieldCard := Nat.one_le_pow width 2 (by omega)
  have gridBound : gridWidth dimension width <= fieldCard :=
    gridWidth_le_fieldCard dimension width widthPositive
  have firstBound : prefixWidth * (8 * width) <=
      fieldCard * (prefixWidth * (8 * width)) := by
    nth_rewrite 1 [← Nat.one_mul (prefixWidth * (8 * width))]
    exact Nat.mul_le_mul_right _ fieldCardPositive
  have secondBound : dimension *
      (prefixWidth * (8 * gridWidth dimension width)) <=
        fieldCard * (dimension * (prefixWidth * 8)) := by
    calc
      dimension * (prefixWidth * (8 * gridWidth dimension width)) =
          (dimension * prefixWidth * 8) * gridWidth dimension width := by ring
      _ <= (dimension * prefixWidth * 8) * fieldCard :=
        Nat.mul_le_mul_left _ gridBound
      _ = fieldCard * (dimension * (prefixWidth * 8)) := by ring
  have thirdBound : dimension * width *
      (2 * gridWidth dimension width) <=
        fieldCard * (dimension * width * 2) := by
    calc
      dimension * width * (2 * gridWidth dimension width) =
          (dimension * width * 2) * gridWidth dimension width := by ring
      _ <= (dimension * width * 2) * fieldCard :=
        Nat.mul_le_mul_left _ gridBound
      _ = fieldCard * (dimension * width * 2) := by ring
  unfold packingCostBound packingCoefficient
  calc
    prefixWidth * (8 * width) +
        dimension * (prefixWidth * (8 * gridWidth dimension width)) +
        dimension * width * (2 * gridWidth dimension width) <=
      fieldCard * (prefixWidth * (8 * width)) +
        fieldCard * (dimension * (prefixWidth * 8)) +
        fieldCard * (dimension * width * 2) :=
      Nat.add_le_add (Nat.add_le_add firstBound secondBound) thirdBound
    _ = fieldCard *
        (prefixWidth * (8 * width) + dimension * (prefixWidth * 8) +
          dimension * width * 2) := by ring

/-- One polynomial envelope for every coefficient in the factored ledger. -/
def coefficientEnvelope (bound : Nat) : Nat :=
  schedulerCoefficient bound bound bound +
    lineCoefficient bound bound +
    packingCoefficient bound bound bound +
    scatterCoefficient bound bound bound +
    gatherCoefficient bound bound bound bound

set_option maxHeartbeats 1000000 in
theorem coefficientEnvelope_le
    (bound : Nat) :
    coefficientEnvelope bound <= 1000000 * (bound + 1) ^ 10 := by
  unfold coefficientEnvelope schedulerCoefficient
    schedulerRecordedCoefficient schedulerStandaloneCoefficient
    freshRankRecordedCoefficient lineCoefficient packingCoefficient
    scatterCoefficient gatherCoefficient
    ForbiddenRanks.guardedProjectiveRankCostBound
    projectiveNormalizationCircuitBound
    candidateOutputCostBound expressionBitsLessCostBound
    candidateRecordWidth
    Routing.recordWidth RoutingMetadata.recordWidth
  dsimp only
  simp only [Routing.recordWidth]
  ring_nf
  omega

/-- Every ledger coefficient is monotone in its bit-width and depth
parameters, and hence lies below the common envelope at any shared upper
bound. -/
theorem coefficients_le_envelope
    (dimension width schedulerDepth prefixWidth keyWidth suffixWidth
      orderWidth routingDepth bound : Nat)
    (dimensionBound : dimension <= bound)
    (widthBound : width <= bound)
    (schedulerDepthBound : schedulerDepth <= bound)
    (prefixWidthBound : prefixWidth <= bound)
    (keyWidthBound : keyWidth <= bound)
    (suffixWidthBound : suffixWidth <= bound)
    (orderWidthBound : orderWidth + 1 <= bound)
    (routingDepthBound : routingDepth <= bound) :
    schedulerCoefficient dimension width schedulerDepth <=
        coefficientEnvelope bound ∧
      lineCoefficient dimension width <= coefficientEnvelope bound ∧
      packingCoefficient prefixWidth dimension width <=
          coefficientEnvelope bound ∧
      scatterCoefficient routingDepth keyWidth suffixWidth <=
          coefficientEnvelope bound ∧
      gatherCoefficient routingDepth keyWidth (orderWidth + 1) width <=
          coefficientEnvelope bound := by
  have schedulerMonotone :
      schedulerCoefficient dimension width schedulerDepth <=
        schedulerCoefficient bound bound bound := by
    unfold schedulerCoefficient schedulerRecordedCoefficient
      schedulerStandaloneCoefficient freshRankRecordedCoefficient
      ForbiddenRanks.guardedProjectiveRankCostBound
      projectiveNormalizationCircuitBound
      candidateOutputCostBound expressionBitsLessCostBound
      candidateRecordWidth
    dsimp only
    gcongr
  have lineMonotone : lineCoefficient dimension width <=
      lineCoefficient bound bound := by
    unfold lineCoefficient
    gcongr
  have packingMonotone : packingCoefficient prefixWidth dimension width <=
      packingCoefficient bound bound bound := by
    unfold packingCoefficient
    gcongr
  have scatterMonotone :
      scatterCoefficient routingDepth keyWidth suffixWidth <=
        scatterCoefficient bound bound bound := by
    unfold scatterCoefficient Routing.recordWidth
    gcongr
  have gatherMonotone :
      gatherCoefficient routingDepth keyWidth (orderWidth + 1) width <=
        gatherCoefficient bound bound bound bound := by
    unfold gatherCoefficient RoutingMetadata.recordWidth Routing.recordWidth
    gcongr
  unfold coefficientEnvelope
  omega

/-- Factored form of every non-resource contribution. -/
def factoredOverhead
    (totalRequests groups prefixWidth dimension width suffixWidth
      schedulerDepth groupBitWidth orderWidth routingDepth : Nat) : Nat :=
  let groupSize := requestGroupSize totalRequests groups
  let keyWidth := IncidenceRouting.incidenceKeyWidth
    groupBitWidth dimension width
  groups * groupSize *
      (networkRecords schedulerDepth *
          schedulerCoefficient dimension width schedulerDepth +
        2 ^ width * lineCoefficient dimension width) +
    totalRequests * (2 ^ width) *
      packingCoefficient prefixWidth dimension width +
    networkRecords routingDepth *
      (scatterCoefficient routingDepth keyWidth suffixWidth +
        gatherCoefficient routingDepth keyWidth (orderWidth + 1) width) +
    totalRequests * (2 ^ width) * width * 5

/-- Sum of the three live record volumes after the two identical
`totalRequests * fieldCardinality` contributions are combined. -/
def overheadVolume
    (totalRequests groups width schedulerDepth routingDepth : Nat) : Nat :=
  let groupSize := requestGroupSize totalRequests groups
  groups * groupSize * (networkRecords schedulerDepth + 2 ^ width) +
    2 * (totalRequests * 2 ^ width) +
    2 * networkRecords routingDepth

/-- Once all widths and depths share a bound, the complete factored ledger is
the live record volume times one explicit degree-ten polynomial envelope. -/
theorem factoredOverhead_le_volume_mul_envelope
    (totalRequests groups prefixWidth dimension width suffixWidth
      schedulerDepth groupBitWidth orderWidth routingDepth bound : Nat)
    (dimensionBound : dimension <= bound)
    (widthBound : width <= bound)
    (schedulerDepthBound : schedulerDepth <= bound)
    (prefixWidthBound : prefixWidth <= bound)
    (keyWidthBound : IncidenceRouting.incidenceKeyWidth
      groupBitWidth dimension width <= bound)
    (suffixWidthBound : suffixWidth <= bound)
    (orderWidthBound : orderWidth + 1 <= bound)
    (routingDepthBound : routingDepth <= bound) :
    factoredOverhead totalRequests groups prefixWidth dimension width
        suffixWidth schedulerDepth groupBitWidth orderWidth routingDepth <=
      overheadVolume totalRequests groups width schedulerDepth routingDepth *
        (coefficientEnvelope bound + 5 * bound) := by
  let groupSize := requestGroupSize totalRequests groups
  let keyWidth := IncidenceRouting.incidenceKeyWidth
    groupBitWidth dimension width
  let coefficient := coefficientEnvelope bound + 5 * bound
  obtain ⟨schedulerBound, lineBound, packingBound, scatterBound,
      gatherBound⟩ := coefficients_le_envelope dimension width schedulerDepth
    prefixWidth keyWidth suffixWidth orderWidth routingDepth bound
    dimensionBound widthBound schedulerDepthBound prefixWidthBound
    keyWidthBound suffixWidthBound orderWidthBound routingDepthBound
  have schedulerBound' :
      schedulerCoefficient dimension width schedulerDepth <= coefficient :=
    schedulerBound.trans (Nat.le_add_right _ _)
  have lineBound' : lineCoefficient dimension width <= coefficient :=
    lineBound.trans (Nat.le_add_right _ _)
  have packingBound' : packingCoefficient prefixWidth dimension width <=
      coefficient := packingBound.trans (Nat.le_add_right _ _)
  have scatterBound' : scatterCoefficient routingDepth keyWidth suffixWidth <=
      coefficient := scatterBound.trans (Nat.le_add_right _ _)
  have gatherBound' :
      gatherCoefficient routingDepth keyWidth (orderWidth + 1) width <=
        coefficient := gatherBound.trans (Nat.le_add_right _ _)
  have decoderBound : width * 5 <= coefficient := by
    dsimp [coefficient]
    have : width * 5 <= 5 * bound := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 5 widthBound
    omega
  have schedulerTermBound :
      groups * requestGroupSize totalRequests groups *
          (networkRecords schedulerDepth *
              schedulerCoefficient dimension width schedulerDepth +
            2 ^ width * lineCoefficient dimension width) <=
        groups * requestGroupSize totalRequests groups *
          (networkRecords schedulerDepth * coefficient +
            2 ^ width * coefficient) := by
    apply Nat.mul_le_mul_left
    exact Nat.add_le_add
      (Nat.mul_le_mul_left _ schedulerBound')
      (Nat.mul_le_mul_left _ lineBound')
  have packingTermBound :
      totalRequests * 2 ^ width *
          packingCoefficient prefixWidth dimension width <=
        totalRequests * 2 ^ width * coefficient :=
    Nat.mul_le_mul_left _ packingBound'
  have routingTermBound :
      networkRecords routingDepth *
          (scatterCoefficient routingDepth keyWidth suffixWidth +
            gatherCoefficient routingDepth keyWidth (orderWidth + 1) width) <=
        networkRecords routingDepth * (coefficient + coefficient) := by
    exact Nat.mul_le_mul_left _
      (Nat.add_le_add scatterBound' gatherBound')
  have decoderTermBound :
      totalRequests * 2 ^ width * width * 5 <=
        totalRequests * 2 ^ width * coefficient := by
    calc
      totalRequests * 2 ^ width * width * 5 =
          totalRequests * 2 ^ width * (width * 5) := by ring
      _ <= totalRequests * 2 ^ width * coefficient :=
        Nat.mul_le_mul_left _ decoderBound
  unfold factoredOverhead overheadVolume
  dsimp only [groupSize, keyWidth]
  change _ <= _ * coefficient
  calc
    groups * requestGroupSize totalRequests groups *
          (networkRecords schedulerDepth *
              schedulerCoefficient dimension width schedulerDepth +
            2 ^ width * lineCoefficient dimension width) +
        totalRequests * 2 ^ width *
          packingCoefficient prefixWidth dimension width +
        networkRecords routingDepth *
          (scatterCoefficient routingDepth
              (IncidenceRouting.incidenceKeyWidth
                groupBitWidth dimension width) suffixWidth +
            gatherCoefficient routingDepth
              (IncidenceRouting.incidenceKeyWidth
                groupBitWidth dimension width) (orderWidth + 1) width) +
        totalRequests * 2 ^ width * width * 5 <=
      groups * requestGroupSize totalRequests groups *
          (networkRecords schedulerDepth * coefficient +
            2 ^ width * coefficient) +
        totalRequests * 2 ^ width * coefficient +
        networkRecords routingDepth * (coefficient + coefficient) +
        totalRequests * 2 ^ width * coefficient := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add schedulerTermBound packingTermBound)
          routingTermBound)
        decoderTermBound
    _ = (groups * requestGroupSize totalRequests groups *
          (networkRecords schedulerDepth + 2 ^ width) +
        2 * (totalRequests * 2 ^ width) +
        2 * networkRecords routingDepth) * coefficient := by ring

/-- The canonical expanded overhead is bounded by the factored record-volume
ledger. -/
theorem overheadCostBound_le_factored
    (totalRequests groups prefixWidth dimension width suffixWidth
      schedulerDepth groupBitWidth orderWidth routingDepth : Nat)
    (widthPositive : 0 < width) :
    overheadCostBound totalRequests groups prefixWidth dimension width
        suffixWidth schedulerDepth groupBitWidth orderWidth routingDepth
        routingDepth <=
      factoredOverhead totalRequests groups prefixWidth dimension width
        suffixWidth schedulerDepth groupBitWidth orderWidth routingDepth := by
  unfold overheadCostBound factoredOverhead
  let groupSize := requestGroupSize totalRequests groups
  let keyWidth := IncidenceRouting.incidenceKeyWidth
    groupBitWidth dimension width
  have schedulerBound := scheduledLineEnumerationCostBound_le
    dimension width schedulerDepth
  have packingBound := packingCostBound_le prefixWidth dimension width
    widthPositive
  rw [scatterRoutingCostBound_eq, gatherRoutingCostBound_eq]
  have schedulerMultiplied := Nat.mul_le_mul_left (groups * groupSize)
    schedulerBound
  have packingMultiplied := Nat.mul_le_mul_left totalRequests packingBound
  dsimp only [groupSize, keyWidth] at schedulerMultiplied packingMultiplied ⊢
  have decoderBound : totalRequests * (nonzeroScalarCount width * width * 5) <=
      totalRequests * (2 ^ width) * width * 5 := by
    have scalarBound : nonzeroScalarCount width <= 2 ^ width := by
      rw [nonzeroScalarCount_eq_two_pow_sub_one widthPositive]
      exact Nat.sub_le _ _
    calc
      totalRequests * (nonzeroScalarCount width * width * 5) =
          totalRequests * nonzeroScalarCount width * width * 5 := by ring
      _ <= totalRequests * (2 ^ width) * width * 5 := by
        gcongr
  calc
    groups * requestGroupSize totalRequests groups *
          scheduledLineEnumerationCostBound dimension width schedulerDepth +
        totalRequests * packingCostBound prefixWidth dimension width +
        networkRecords routingDepth *
          scatterCoefficient routingDepth
            (IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width)
            suffixWidth +
        networkRecords routingDepth *
          gatherCoefficient routingDepth
            (IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width)
            (orderWidth + 1) width +
        totalRequests * (nonzeroScalarCount width * width * 5) <=
      groups * requestGroupSize totalRequests groups *
          (networkRecords schedulerDepth *
              schedulerCoefficient dimension width schedulerDepth +
            2 ^ width * lineCoefficient dimension width) +
        totalRequests *
          (2 ^ width * packingCoefficient prefixWidth dimension width) +
        networkRecords routingDepth *
          scatterCoefficient routingDepth
            (IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width)
            suffixWidth +
        networkRecords routingDepth *
          gatherCoefficient routingDepth
            (IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width)
            (orderWidth + 1) width +
        totalRequests * (2 ^ width) * width * 5 := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add schedulerMultiplied packingMultiplied)
              (Nat.le_refl _))
            (Nat.le_refl _))
          decoderBound
    _ = groups * requestGroupSize totalRequests groups *
          (networkRecords schedulerDepth *
              schedulerCoefficient dimension width schedulerDepth +
            2 ^ width * lineCoefficient dimension width) +
        totalRequests * 2 ^ width *
          packingCoefficient prefixWidth dimension width +
        networkRecords routingDepth *
          (scatterCoefficient routingDepth
              (IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width)
              suffixWidth +
            gatherCoefficient routingDepth
              (IncidenceRouting.incidenceKeyWidth groupBitWidth dimension width)
              (orderWidth + 1) width) +
        totalRequests * 2 ^ width * width * 5 := by ring

end OverheadBound
end MassProduction
end Algebraic
