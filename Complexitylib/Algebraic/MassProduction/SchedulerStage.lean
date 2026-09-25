/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.ForbiddenRanks
public import Complexitylib.Algebraic.MassProduction.LowDegree

/-!
# One complete constructive greedy-scheduler stage

This module builds the fixed-wire preprocessing omitted by the
rank-list-level selector.  A stage input contains a power-of-two array of
previously occupied points followed by the current target.  An explicit
coordinatewise `GF(2^width)` addition circuit forms `point - target` (the same
as `point + target` in characteristic two), and the verified guarded-rank,
sort, least-missing, and unrank pipeline selects a disjoint recovery-line
direction.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace SchedulerStage

open scoped LinearAlgebra.Projectivization
open Sorting

/-! ## Coordinatewise packed vector addition -/

/-- Reorder one coordinate pair into the pair-of-whole-vectors layout. -/
def vectorCoordinatePairIndex
    (dimension width : Nat)
    (coordinate : Fin dimension)
    (input : Fin (2 * width)) : Fin (2 * (dimension * width)) :=
  let sideAndBit :=
    (finProdFinEquiv (m := 2) (n := width)).symm input
  finProdFinEquiv
    (sideAndBit.1, finProdFinEquiv (coordinate, sideAndBit.2))

/-- Pure semantics of coordinatewise packed field addition. -/
def binaryExtensionVectorAddBits
    (dimension width : Nat)
    (input : Fin (2 * (dimension * width)) -> Bool) :
    Fin (dimension * width) -> Bool :=
  fun output =>
    let coordinateAndBit :=
      (finProdFinEquiv (m := dimension) (n := width)).symm output
    binaryExtensionAddBits
      (input ∘ vectorCoordinatePairIndex
        dimension width coordinateAndBit.1) coordinateAndBit.2

/-- Exact gate count of one vector-addition coordinate circuit. -/
@[reducible] def vectorAdditionCoordinateGateCount
    (width : Nat) : Nat :=
  ∑ output : Fin width, additionCoordinateGateCount output

/-- Add two packed extension-field vectors coordinatewise. -/
def binaryExtensionVectorAddCircuit
    (dimension width : Nat) :
    Circuit DeMorgan.signature (2 * (dimension * width))
      (dimension * width) :=
  Circuit.parallelFinVector dimension width fun coordinate =>
      (binaryExtensionAddCircuit width).mapInputs
        (vectorCoordinatePairIndex dimension width coordinate)

@[simp] theorem binaryExtensionVectorAddCircuit_size
    (dimension width : Nat) :
    (binaryExtensionVectorAddCircuit dimension width).size =
      ∑ _coordinate : Fin dimension, vectorAdditionCoordinateGateCount width := by
  simp [binaryExtensionVectorAddCircuit, vectorAdditionCoordinateGateCount]

@[simp] theorem binaryExtensionVectorAddCircuit_eval
    (input : Fin (2 * (dimension * width)) -> Bool) :
    (binaryExtensionVectorAddCircuit dimension width).eval
        DeMorgan.interpretation input =
      binaryExtensionVectorAddBits dimension width input := by
  funext output
  obtain ⟨⟨coordinate, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := dimension) (n := width)).surjective output
  rw [binaryExtensionVectorAddCircuit,
    Circuit.eval_parallelFinVector, Circuit.eval_mapInputs,
    binaryExtensionAddCircuit_eval]
  unfold binaryExtensionVectorAddBits
  rw [Equiv.symm_apply_apply]

@[simp] theorem binaryExtensionVectorAddCircuit_cost :
    (binaryExtensionVectorAddCircuit dimension width).cost
        DeMorgan.standardCost = dimension * (4 * width) := by
  rw [binaryExtensionVectorAddCircuit,
    Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_mapInputs, binaryExtensionAddCircuit_cost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]

/-- A pair of whole packed vectors, with the left vector first. -/
def binaryExtensionVectorPairBits
    (left right : Fin (dimension * width) -> Bool) :
    Fin (2 * (dimension * width)) -> Bool :=
  binaryExtensionPairBits left right

theorem vectorCoordinatePair_of_vectorPairBits
    (left right : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) :
    binaryExtensionVectorPairBits left right ∘
        vectorCoordinatePairIndex dimension width coordinate =
      binaryExtensionPairBits
        (fun bit => left (finProdFinEquiv (coordinate, bit)))
        (fun bit => right (finProdFinEquiv (coordinate, bit))) := by
  funext input
  obtain ⟨⟨side, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := width)).surjective input
  unfold binaryExtensionVectorPairBits
  simp only [Function.comp_apply]
  rw [show vectorCoordinatePairIndex dimension width coordinate
      (finProdFinEquiv (side, bit)) =
        finProdFinEquiv (side, finProdFinEquiv (coordinate, bit)) by
    simp [vectorCoordinatePairIndex]]
  simp [binaryExtensionPairBits]

/-- Packed vector addition agrees exactly with field-vector addition. -/
theorem binaryExtensionVectorAddCircuit_eval_vectorBits
    (widthPositive : 0 < width)
    (left right : Fin dimension -> BinaryExtension width) :
    (binaryExtensionVectorAddCircuit dimension width).eval
        DeMorgan.interpretation
        (binaryExtensionVectorPairBits
          (binaryExtensionVectorBits widthPositive left)
          (binaryExtensionVectorBits widthPositive right)) =
      binaryExtensionVectorBits widthPositive (left + right) := by
  rw [binaryExtensionVectorAddCircuit_eval]
  funext output
  obtain ⟨⟨coordinate, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := dimension) (n := width)).surjective output
  unfold binaryExtensionVectorAddBits
  rw [Equiv.symm_apply_apply]
  change binaryExtensionAddBits
      (binaryExtensionVectorPairBits
          (binaryExtensionVectorBits widthPositive left)
          (binaryExtensionVectorBits widthPositive right) ∘
        vectorCoordinatePairIndex dimension width coordinate) bit =
    binaryExtensionVectorBits widthPositive (left + right)
      (finProdFinEquiv (coordinate, bit))
  have coordinateInput :
      binaryExtensionVectorPairBits
          (binaryExtensionVectorBits widthPositive left)
          (binaryExtensionVectorBits widthPositive right) ∘
          vectorCoordinatePairIndex dimension width coordinate =
        binaryExtensionPairBits
          (decodeBinaryExtension widthPositive (left coordinate))
          (decodeBinaryExtension widthPositive (right coordinate)) := by
    rw [vectorCoordinatePair_of_vectorPairBits]
    congr 1 <;> funext localBit <;>
      simp [binaryExtensionVectorBits]
  rw [coordinateInput]
  unfold binaryExtensionVectorBits
  rw [Equiv.symm_apply_apply]
  simp only [Pi.add_apply]
  apply congrFun
  apply encodeBinaryExtension_injective widthPositive
  rw [encode_binaryExtensionAddBits,
    binaryExtensionPairInput_pairBits_zero,
    binaryExtensionPairInput_pairBits_one,
    encodeBinaryExtension_decode, encodeBinaryExtension_decode]
  rw [encodeBinaryExtension_decode]

/-! ## Fixed input layout for the occupied points and target -/

/-- One bit of the point block in a `(points..., target)` stage input. -/
def stagePointInputIndex
    (depth vectorWidth : Nat)
    (record : Fin (networkRecords depth))
    (bit : Fin vectorWidth) :
    Fin ((networkRecords depth + 1) * vectorWidth) :=
  blockPrefixIndex (finProdFinEquiv (record, bit))

/-- One bit of the final target block in a `(points..., target)` stage
input. -/
def stageTargetInputIndex
    (depth vectorWidth : Nat)
    (bit : Fin vectorWidth) :
    Fin ((networkRecords depth + 1) * vectorWidth) :=
  blockSuffixIndex bit

/-- Inputs for one vector subtraction/addition inside the global stage
layout. -/
def stageDifferenceInputIndex
    (depth vectorWidth : Nat)
    (record : Fin (networkRecords depth))
    (input : Fin (2 * vectorWidth)) :
    Fin ((networkRecords depth + 1) * vectorWidth) :=
  let sideAndBit :=
    (finProdFinEquiv (m := 2) (n := vectorWidth)).symm input
  Fin.cases
    (stagePointInputIndex depth vectorWidth record sideAndBit.2)
    (fun _ => stageTargetInputIndex depth vectorWidth sideAndBit.2)
    sideAndBit.1

/-- Raw parallel circuit before spelling its output count as
`networkBits`. -/
def pointTargetDifferenceArrayRawCircuit
    (dimension width depth : Nat) :
    Circuit DeMorgan.signature
      ((networkRecords depth + 1) * (dimension * width))
      (networkRecords depth * (dimension * width)) :=
  Circuit.parallelFinVector (networkRecords depth) (dimension * width) fun record =>
      (binaryExtensionVectorAddCircuit dimension width).mapInputs
        (stageDifferenceInputIndex depth (dimension * width) record)

@[simp] theorem pointTargetDifferenceArrayRawCircuit_size
    (dimension width depth : Nat) :
    (pointTargetDifferenceArrayRawCircuit dimension width depth).size =
      ∑ _record : Fin (networkRecords depth), ∑ _coordinate : Fin dimension, vectorAdditionCoordinateGateCount width := by
  simp [pointTargetDifferenceArrayRawCircuit, vectorAdditionCoordinateGateCount]

/-- Compute all point-minus-target vectors in parallel. -/
def pointTargetDifferenceArrayCircuit
    (dimension width depth : Nat) :
    Circuit DeMorgan.signature
      ((networkRecords depth + 1) * (dimension * width))
      (networkRecords depth * (dimension * width)) :=
  pointTargetDifferenceArrayRawCircuit dimension width depth

@[simp] theorem pointTargetDifferenceArrayCircuit_size
    (dimension width depth : Nat) :
    (pointTargetDifferenceArrayCircuit dimension width depth).size =
      ∑ _record : Fin (networkRecords depth), ∑ _coordinate : Fin dimension, vectorAdditionCoordinateGateCount width := by
  simp [pointTargetDifferenceArrayCircuit, vectorAdditionCoordinateGateCount]

@[simp] theorem pointTargetDifferenceArrayRawCircuit_eval_apply
    (input : Fin ((networkRecords depth + 1) * (dimension * width)) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin (dimension * width)) :
    (pointTargetDifferenceArrayRawCircuit dimension width depth).eval
        DeMorgan.interpretation input
        (finProdFinEquiv (record, bit)) =
      (binaryExtensionVectorAddCircuit dimension width).eval
        DeMorgan.interpretation
        (input ∘ stageDifferenceInputIndex
          depth (dimension * width) record) bit := by
  rw [pointTargetDifferenceArrayRawCircuit,
    Circuit.eval_parallelFinVector, Circuit.eval_mapInputs]

/-- Reading one generated difference block evaluates the corresponding
vector-addition circuit on that point and the shared target. -/
theorem pointTargetDifferenceArrayCircuit_eval_apply
    (input : Fin ((networkRecords depth + 1) * (dimension * width)) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin (dimension * width)) :
    (pointTargetDifferenceArrayCircuit dimension width depth).eval
        DeMorgan.interpretation input
        (finProdFinEquiv (record, bit)) =
      (binaryExtensionVectorAddCircuit dimension width).eval
        DeMorgan.interpretation
        (input ∘ stageDifferenceInputIndex
          depth (dimension * width) record) bit := by
  rw [pointTargetDifferenceArrayCircuit]
  exact pointTargetDifferenceArrayRawCircuit_eval_apply input record bit

@[simp] theorem pointTargetDifferenceArrayCircuit_cost :
    (pointTargetDifferenceArrayCircuit dimension width depth).cost
        DeMorgan.standardCost =
      networkRecords depth * (dimension * (4 * width)) := by
  rw [pointTargetDifferenceArrayCircuit,
    pointTargetDifferenceArrayRawCircuit,
    Circuit.cost_parallelFinVector]
  simp only [Circuit.cost_mapInputs, binaryExtensionVectorAddCircuit_cost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]

theorem stageDifferenceInput_eq_pair
    (input : Fin ((networkRecords depth + 1) * vectorWidth) -> Bool)
    (point : Fin vectorWidth -> Bool)
    (target : Fin vectorWidth -> Bool)
    (record : Fin (networkRecords depth))
    (pointBits : ∀ bit,
      input (stagePointInputIndex depth vectorWidth record bit) = point bit)
    (targetBits : ∀ bit,
      input (stageTargetInputIndex depth vectorWidth bit) = target bit) :
    input ∘ stageDifferenceInputIndex depth vectorWidth record =
      binaryExtensionPairBits point target := by
  funext flat
  obtain ⟨⟨side, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := vectorWidth)).surjective flat
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · simpa [Function.comp_apply, stageDifferenceInputIndex,
      binaryExtensionPairBits] using pointBits bit
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    simp only [Function.comp_apply, stageDifferenceInputIndex,
      Equiv.symm_apply_apply, Fin.cases_succ]
    unfold binaryExtensionPairBits
    rw [Equiv.symm_apply_apply, Fin.cases_succ]
    exact targetBits bit

/-- Row-major packed bits of the occupied-point array. -/
noncomputable def packedPointArrayBits
    (widthPositive : 0 < width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width) :
    Fin (networkRecords depth * (dimension * width)) -> Bool :=
  fun flat =>
    let recordAndBit :=
      (finProdFinEquiv
        (m := networkRecords depth) (n := dimension * width)).symm flat
    binaryExtensionVectorBits widthPositive (points recordAndBit.1)
      recordAndBit.2

/-- Canonical `(points..., target)` input expected by a scheduler stage. -/
noncomputable def schedulerStageInputBits
    (widthPositive : 0 < width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width) :
    Fin ((networkRecords depth + 1) * (dimension * width)) -> Bool :=
  fun flat =>
    Fin.append (packedPointArrayBits widthPositive points)
      (binaryExtensionVectorBits widthPositive target)
      (Fin.cast (Nat.succ_mul (networkRecords depth)
        (dimension * width)) flat)

@[simp] theorem schedulerStageInputBits_point
    (widthPositive : 0 < width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (record : Fin (networkRecords depth))
    (bit : Fin (dimension * width)) :
  schedulerStageInputBits widthPositive points target
        (stagePointInputIndex depth (dimension * width) record bit) =
      binaryExtensionVectorBits widthPositive (points record) bit := by
  unfold schedulerStageInputBits
  rw [show Fin.cast
      (Nat.succ_mul (networkRecords depth) (dimension * width))
      (stagePointInputIndex depth (dimension * width) record bit) =
        Fin.castAdd (dimension * width) (finProdFinEquiv (record, bit)) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left]
  simp [packedPointArrayBits]

@[simp] theorem schedulerStageInputBits_target
    (widthPositive : 0 < width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (bit : Fin (dimension * width)) :
    schedulerStageInputBits widthPositive points target
        (stageTargetInputIndex depth (dimension * width) bit) =
      binaryExtensionVectorBits widthPositive target bit := by
  unfold schedulerStageInputBits
  rw [show Fin.cast
      (Nat.succ_mul (networkRecords depth) (dimension * width))
      (stageTargetInputIndex depth (dimension * width) bit) =
        Fin.natAdd (networkRecords depth * (dimension * width)) bit by
    apply Fin.ext
    rfl]
  rw [Fin.append_right]

/-- With correctly encoded point and target blocks, the preprocessing circuit
emits the packed characteristic-two difference `point - target`. -/
theorem pointTargetDifferenceArrayCircuit_eval_vectorBits
    (widthPositive : 0 < width)
    (input : Fin ((networkRecords depth + 1) *
      (dimension * width)) -> Bool)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (pointBits : ∀ record bit,
      input (stagePointInputIndex depth (dimension * width) record bit) =
        binaryExtensionVectorBits widthPositive (points record) bit)
    (targetBits : ∀ bit,
      input (stageTargetInputIndex depth (dimension * width) bit) =
        binaryExtensionVectorBits widthPositive target bit)
    (record : Fin (networkRecords depth)) :
    directProductInput
        ((pointTargetDifferenceArrayCircuit dimension width depth).eval
          DeMorgan.interpretation input) record =
      binaryExtensionVectorBits widthPositive (points record - target) := by
  have pairInput := stageDifferenceInput_eq_pair input
    (binaryExtensionVectorBits widthPositive (points record))
    (binaryExtensionVectorBits widthPositive target) record
    (pointBits record) targetBits
  change input ∘
      stageDifferenceInputIndex depth (dimension * width) record =
    binaryExtensionVectorPairBits
      (binaryExtensionVectorBits widthPositive (points record))
      (binaryExtensionVectorBits widthPositive target) at pairInput
  change (fun bit =>
    (pointTargetDifferenceArrayCircuit dimension width depth).eval
      DeMorgan.interpretation input (finProdFinEquiv (record, bit))) =
    binaryExtensionVectorBits widthPositive (points record - target)
  funext bit
  rw [pointTargetDifferenceArrayCircuit_eval_apply]
  rw [pairInput,
    binaryExtensionVectorAddCircuit_eval_vectorBits widthPositive]
  rw [show points record - target = points record + target by
    funext coordinate
    simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg,
      neg_eq_self_of_char_two]]

/-- Point-array positions that differ from the current target.  Positions
equal to the target are valid padding and forbid no projective direction. -/
noncomputable def pointDifferentIndices
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width) :
    Finset (Fin (networkRecords depth)) := by
  classical
  exact Finset.univ.filter fun record => points record ≠ target

/-- For the canonical stage input, nonzero generated differences occur
exactly at the non-padding point positions. -/
theorem nonzeroVectorIndices_differenceArray
    (widthPositive : 0 < width)
    (input : Fin ((networkRecords depth + 1) *
      (dimension * width)) -> Bool)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (pointBits : ∀ record bit,
      input (stagePointInputIndex depth (dimension * width) record bit) =
        binaryExtensionVectorBits widthPositive (points record) bit)
    (targetBits : ∀ bit,
      input (stageTargetInputIndex depth (dimension * width) bit) =
        binaryExtensionVectorBits widthPositive target bit) :
    ForbiddenRanks.nonzeroVectorIndices
        ((pointTargetDifferenceArrayCircuit dimension width depth).eval
          DeMorgan.interpretation input) =
      pointDifferentIndices points target := by
  classical
  ext record
  simp only [ForbiddenRanks.nonzeroVectorIndices,
    pointDifferentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [pointTargetDifferenceArrayCircuit_eval_vectorBits
    widthPositive input points target pointBits targetBits record]
  rw [binaryExtensionVectorBits_ne_zero_iff]
  exact sub_ne_zero

/-! ## The complete stage and its geometric correctness -/

/-- Complete fixed-wire circuit for one greedy scheduling stage. -/
noncomputable def schedulerStageCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) :=
  (ForbiddenRanks.freshDirectionFromDifferencesCircuit
      dimension widthPositive depth).comp
    (pointTargetDifferenceArrayCircuit dimension width depth)

/-- Uniform polynomial ledger for one fully expanded scheduler stage. -/
def schedulerStageCostBound
    (dimension width depth : Nat) : Nat :=
  networkRecords depth * (dimension * (4 * width)) +
    ForbiddenRanks.freshDirectionFromDifferencesCostBound
      dimension width depth

theorem schedulerStageCircuit_cost_le
    (widthPositive : 0 < width) :
    (schedulerStageCircuit dimension widthPositive depth).cost
        DeMorgan.standardCost ≤
      schedulerStageCostBound dimension width depth := by
  unfold schedulerStageCostBound
  rw [show
    (schedulerStageCircuit dimension widthPositive depth).cost
        DeMorgan.standardCost =
      (pointTargetDifferenceArrayCircuit dimension width depth).cost
          DeMorgan.standardCost +
        (ForbiddenRanks.freshDirectionFromDifferencesCircuit
          dimension widthPositive depth).cost DeMorgan.standardCost by
    exact Circuit.cost_comp _ _ _]
  rw [pointTargetDifferenceArrayCircuit_cost]
  exact Nat.add_le_add_left
    (ForbiddenRanks.freshDirectionFromDifferencesCircuit_cost_le
      widthPositive) _

/-- One fully explicit stage selects a canonical direction whose punctured
line avoids every point represented in the input array. -/
theorem schedulerStageCircuit_disjoint_of_nonzero_capacity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin ((networkRecords depth + 1) *
      (dimension * width)) -> Bool)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (used : Finset (Fin dimension -> BinaryExtension width))
    (pointBits : ∀ record bit,
      input (stagePointInputIndex depth (dimension * width) record bit) =
        binaryExtensionVectorBits widthPositive (points record) bit)
    (targetBits : ∀ bit,
      input (stageTargetInputIndex depth (dimension * width) bit) =
        binaryExtensionVectorBits widthPositive target bit)
    (usedCovered : ∀ point, point ∈ used ->
      ∃ record, points record = point)
    (capacity : (pointDifferentIndices points target).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (schedulerStageCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        used := by
  let differences :=
    (pointTargetDifferenceArrayCircuit dimension width depth).eval
      DeMorgan.interpretation input
  have covers : ∀ point, point ∈ used ->
      ∃ record : Fin (networkRecords depth),
        directProductInput differences record =
          binaryExtensionVectorBits widthPositive (point - target) := by
    intro point pointUsed
    obtain ⟨record, recordEquality⟩ := usedCovered point pointUsed
    refine ⟨record, ?_⟩
    rw [← recordEquality]
    exact pointTargetDifferenceArrayCircuit_eval_vectorBits
      widthPositive input points target pointBits targetBits record
  obtain ⟨direction, directionKey, disjoint⟩ :=
    ForbiddenRanks.freshDirectionFromDifferencesCircuit_disjoint_of_nonzero_capacity
      widthPositive widthAtLeastTwo target used differences covers (by
        rw [show ForbiddenRanks.nonzeroVectorIndices differences =
            pointDifferentIndices points target by
          dsimp only [differences]
          exact nonzeroVectorIndices_differenceArray
            widthPositive input points target pointBits targetBits]
        exact capacity)
  refine ⟨direction, ?_, disjoint⟩
  exact (Circuit.eval_comp (I := DeMorgan.interpretation)
    (ForbiddenRanks.freshDirectionFromDifferencesCircuit
      dimension widthPositive depth)
    (pointTargetDifferenceArrayCircuit dimension width depth)
    input).trans directionKey

/-- The total-array capacity condition is a convenient sufficient form of
one-stage correctness. -/
theorem schedulerStageCircuit_disjoint
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin ((networkRecords depth + 1) *
      (dimension * width)) -> Bool)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (used : Finset (Fin dimension -> BinaryExtension width))
    (pointBits : ∀ record bit,
      input (stagePointInputIndex depth (dimension * width) record bit) =
        binaryExtensionVectorBits widthPositive (points record) bit)
    (targetBits : ∀ bit,
      input (stageTargetInputIndex depth (dimension * width) bit) =
        binaryExtensionVectorBits widthPositive target bit)
    (usedCovered : ∀ point, point ∈ used ->
      ∃ record, points record = point)
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (schedulerStageCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        used := by
  apply schedulerStageCircuit_disjoint_of_nonzero_capacity
    widthPositive widthAtLeastTwo input points target used
    pointBits targetBits usedCovered
  calc
    (pointDifferentIndices points target).card ≤
        (Finset.univ : Finset (Fin (networkRecords depth))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = networkRecords depth := by simp
    _ < Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := capacity

/-- Public sentinel-aware vector-level form of one constructive stage. -/
theorem schedulerStageCircuit_disjoint_vectorInput_of_nonzero_capacity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (used : Finset (Fin dimension -> BinaryExtension width))
    (usedCovered : ∀ point, point ∈ used ->
      ∃ record, points record = point)
    (capacity : (pointDifferentIndices points target).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (schedulerStageCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation
          (schedulerStageInputBits widthPositive points target) =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        used := by
  exact schedulerStageCircuit_disjoint_of_nonzero_capacity
    widthPositive widthAtLeastTwo
    (schedulerStageInputBits widthPositive points target) points target used
    (schedulerStageInputBits_point widthPositive points target)
    (schedulerStageInputBits_target widthPositive points target)
    usedCovered capacity

/-- Public vector-level form under total-array capacity. -/
theorem schedulerStageCircuit_disjoint_vectorInput
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (used : Finset (Fin dimension -> BinaryExtension width))
    (usedCovered : ∀ point, point ∈ used ->
      ∃ record, points record = point)
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (schedulerStageCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation
          (schedulerStageInputBits widthPositive points target) =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        used := by
  exact schedulerStageCircuit_disjoint widthPositive widthAtLeastTwo
    (schedulerStageInputBits widthPositive points target) points target used
    (schedulerStageInputBits_point widthPositive points target)
    (schedulerStageInputBits_target widthPositive points target)
    usedCovered capacity

/-- The finite set of points appearing in a packed stage array.  Its
decidable equality is kept local to this definition. -/
noncomputable def pointArraySet
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width) :
    Finset (Fin dimension -> BinaryExtension width) := by
  classical
  exact Finset.univ.image points

/-- In particular, a sentinel-aware stage avoids the entire supplied point
array. -/
theorem schedulerStageCircuit_disjoint_all_points_of_nonzero_capacity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (capacity : (pointDifferentIndices points target).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (schedulerStageCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation
          (schedulerStageInputBits widthPositive points target) =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        (pointArraySet points) := by
  classical
  apply schedulerStageCircuit_disjoint_vectorInput_of_nonzero_capacity
    widthPositive widthAtLeastTwo points target
  intro point pointMember
  unfold pointArraySet at pointMember
  rw [Finset.mem_image] at pointMember
  obtain ⟨record, _, equality⟩ := pointMember
  exact ⟨record, equality⟩
  exact capacity

/-- A stage avoids the entire supplied power-of-two point array under total
array capacity. -/
theorem schedulerStageCircuit_disjoint_all_points
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (schedulerStageCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation
          (schedulerStageInputBits widthPositive points target) =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        (pointArraySet points) := by
  classical
  apply schedulerStageCircuit_disjoint_vectorInput
    widthPositive widthAtLeastTwo points target
  · intro point pointMember
    unfold pointArraySet at pointMember
    rw [Finset.mem_image] at pointMember
    obtain ⟨record, _, equality⟩ := pointMember
    exact ⟨record, equality⟩
  · exact capacity

end SchedulerStage
end MassProduction
end Algebraic
