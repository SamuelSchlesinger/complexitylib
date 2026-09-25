/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.LineEnumeration

/-!
# Unrolled greedy scheduler circuits

This module unrolls the manuscript's greedy scheduler over a fixed request
group.  The state retains all previously emitted punctured-line points and
the next stage pads its power-of-two sorting array with the current target;
those padding positions generate zero differences and hence sentinel ranks.

No new global field or finite-enumeration instances are introduced.  The
request count, sorter depth, and slot-capacity proof are ordinary parameters
of the nonuniform circuit family.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace SchedulerIteration

open scoped LinearAlgebra.Projectivization
open Sorting
open LineEnumeration

/-- Packed width of one affine-space point. -/
@[reducible] def pointBitWidth (dimension width : Nat) : Nat :=
  dimension * width

/-- Number of packed bits emitted for one punctured line. -/
@[reducible] noncomputable def lineBitWidth
    (dimension width : Nat) : Nat :=
  nonzeroScalarCount width * pointBitWidth dimension width

/-- Total gate count of the recursively unrolled circuit. -/
@[reducible] noncomputable def greedyScheduleGateCount
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) : Nat -> Nat
  | 0 => 0
  | requests + 1 =>
      greedyScheduleGateCount dimension widthPositive depth requests +
        (scheduledLineEnumerationCircuit
          dimension widthPositive depth).size

/-- Row-major target-array encoding. -/
noncomputable def targetArrayBits
    (widthPositive : 0 < width)
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width) :
    Fin (requests * pointBitWidth dimension width) -> Bool :=
  fun flat =>
    let targetAndBit := (finProdFinEquiv
      (m := requests) (n := pointBitWidth dimension width)).symm flat
    binaryExtensionVectorBits widthPositive (targets targetAndBit.1)
      targetAndBit.2

@[simp] theorem targetArrayBits_apply
    (widthPositive : 0 < width)
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width)
    (request : Fin requests)
    (bit : Fin (pointBitWidth dimension width)) :
    targetArrayBits widthPositive targets
        (finProdFinEquiv (request, bit)) =
      binaryExtensionVectorBits widthPositive (targets request) bit := by
  simp [targetArrayBits]

/-- Map a full target array to its initial request prefix. -/
def targetPrefixInputIndex
    (requests pointWidth : Nat) :
    Fin (requests * pointWidth) -> Fin ((requests + 1) * pointWidth) :=
  blockPrefixIndex

/-- Select the final target from a nonempty target array. -/
def currentTargetInputIndex
    (requests pointWidth : Nat) :
    Fin pointWidth -> Fin ((requests + 1) * pointWidth) :=
  blockSuffixIndex

theorem targetPrefixInputIndex_apply
    (request : Fin requests)
    (bit : Fin pointWidth) :
    targetPrefixInputIndex requests pointWidth
        (finProdFinEquiv (request, bit)) =
      finProdFinEquiv (request.castSucc, bit) := by
  apply Fin.ext
  simp [targetPrefixInputIndex, blockPrefixIndex, finProdFinEquiv]

theorem currentTargetInputIndex_apply
    (bit : Fin pointWidth) :
    currentTargetInputIndex requests pointWidth bit =
      finProdFinEquiv (Fin.last requests, bit) := by
  apply Fin.ext
  simp [currentTargetInputIndex, blockSuffixIndex, finProdFinEquiv,
    Nat.mul_comm, Nat.add_comm]

theorem targetArrayBits_prefix
    (widthPositive : 0 < width)
    (targets : Fin (requests + 1) ->
      Fin dimension -> BinaryExtension width) :
    targetArrayBits widthPositive targets ∘
        targetPrefixInputIndex requests
          (pointBitWidth dimension width) =
      targetArrayBits widthPositive
        (fun request : Fin requests => targets request.castSucc) := by
  funext flat
  obtain ⟨⟨request, bit⟩, rfl⟩ :=
    (finProdFinEquiv
      (m := requests)
      (n := pointBitWidth dimension width)).surjective flat
  rw [Function.comp_apply, targetPrefixInputIndex_apply,
    targetArrayBits_apply, targetArrayBits_apply]

theorem targetArrayBits_current
    (widthPositive : 0 < width)
    (targets : Fin (requests + 1) ->
      Fin dimension -> BinaryExtension width) :
    targetArrayBits widthPositive targets ∘
        currentTargetInputIndex requests
          (pointBitWidth dimension width) =
      binaryExtensionVectorBits widthPositive
        (targets (Fin.last requests)) := by
  funext bit
  rw [Function.comp_apply, currentTargetInputIndex_apply,
    targetArrayBits_apply]

/-- Construct the next stage input from the retained prefix-line outputs and
the current target.  The first `priorRequests * (q - 1)` point records are
live; every remaining point record and the final target record read the
current target block. -/
noncomputable def greedyStageInputIndex
    (dimension width depth priorRequests : Nat)
    (_priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (flat : Fin ((networkRecords depth + 1) *
      pointBitWidth dimension width)) :
    Fin (priorRequests * lineBitWidth dimension width +
      pointBitWidth dimension width) :=
  let recordAndBit := (finProdFinEquiv
    (m := networkRecords depth + 1)
    (n := pointBitWidth dimension width)).symm flat
  if live : recordAndBit.1.val <
      priorRequests * nonzeroScalarCount width then
    ⟨recordAndBit.1.val * pointBitWidth dimension width +
        recordAndBit.2.val,
      by
        have bitBound := recordAndBit.2.isLt
        have recordBound : recordAndBit.1.val + 1 ≤
            priorRequests * nonzeroScalarCount width := by omega
        have liveBits :
            recordAndBit.1.val * pointBitWidth dimension width +
                recordAndBit.2.val <
              priorRequests * lineBitWidth dimension width := by
          calc
            recordAndBit.1.val * pointBitWidth dimension width +
                recordAndBit.2.val <
                recordAndBit.1.val * pointBitWidth dimension width +
                  pointBitWidth dimension width :=
              Nat.add_lt_add_left bitBound _
            _ = (recordAndBit.1.val + 1) *
                pointBitWidth dimension width := by ring
            _ ≤ (priorRequests * nonzeroScalarCount width) *
                pointBitWidth dimension width :=
              Nat.mul_le_mul_right _ recordBound
            _ = priorRequests * lineBitWidth dimension width := by
              unfold lineBitWidth
              ring
        exact liveBits.trans_le (Nat.le_add_right _ _)⟩
  else
    ⟨priorRequests * lineBitWidth dimension width +
        recordAndBit.2.val,
      by
        have bitBound := recordAndBit.2.isLt
        omega⟩

/-- Free rewiring from the retained state to one scheduler-stage input. -/
noncomputable def greedyStageInputCircuit
    (dimension width depth priorRequests : Nat)
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth) :
    Circuit DeMorgan.signature
      (priorRequests * lineBitWidth dimension width +
        pointBitWidth dimension width)
      0
      ((networkRecords depth + 1) * pointBitWidth dimension width) :=
  (Circuit.id DeMorgan.signature
    (priorRequests * lineBitWidth dimension width +
      pointBitWidth dimension width)).mapOutputs
        (greedyStageInputIndex dimension width depth priorRequests priorFits)

@[simp] theorem greedyStageInputCircuit_cost
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth) :
    (greedyStageInputCircuit dimension width depth priorRequests
      priorFits).cost DeMorgan.standardCost = 0 := by
  simp [greedyStageInputCircuit]

theorem greedyStageInputIndex_point_of_padding
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (record : Fin (networkRecords depth))
    (bit : Fin (pointBitWidth dimension width))
    (padding : ¬record.val <
      priorRequests * nonzeroScalarCount width) :
    greedyStageInputIndex dimension width depth priorRequests priorFits
        (SchedulerStage.stagePointInputIndex depth
          (pointBitWidth dimension width) record bit) =
      Fin.natAdd (priorRequests * lineBitWidth dimension width) bit := by
  have decoded :
      (finProdFinEquiv
        (m := networkRecords depth + 1)
        (n := pointBitWidth dimension width)).symm
          (SchedulerStage.stagePointInputIndex depth
            (pointBitWidth dimension width) record bit) =
        (record.castSucc, bit) := by
    have flattened : SchedulerStage.stagePointInputIndex depth
          (pointBitWidth dimension width) record bit =
        finProdFinEquiv (record.castSucc, bit) := by
      apply Fin.ext
      simp [SchedulerStage.stagePointInputIndex, blockPrefixIndex,
        finProdFinEquiv]
    rw [flattened, Equiv.symm_apply_apply]
  unfold greedyStageInputIndex
  simp only [decoded]
  have paddingCast : ¬↑record.castSucc <
      priorRequests * nonzeroScalarCount width := by
    exact padding
  rw [dite_eq_right paddingCast]
  apply Fin.ext
  rfl

theorem greedyStageInputIndex_target
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (bit : Fin (pointBitWidth dimension width)) :
    greedyStageInputIndex dimension width depth priorRequests priorFits
        (SchedulerStage.stageTargetInputIndex depth
          (pointBitWidth dimension width) bit) =
      Fin.natAdd (priorRequests * lineBitWidth dimension width) bit := by
  have decoded :
      (finProdFinEquiv
        (m := networkRecords depth + 1)
        (n := pointBitWidth dimension width)).symm
          (SchedulerStage.stageTargetInputIndex depth
            (pointBitWidth dimension width) bit) =
        (Fin.last (networkRecords depth), bit) := by
    have flattened : SchedulerStage.stageTargetInputIndex depth
          (pointBitWidth dimension width) bit =
        finProdFinEquiv (Fin.last (networkRecords depth), bit) := by
      apply Fin.ext
      simp [SchedulerStage.stageTargetInputIndex, blockSuffixIndex,
        finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [flattened, Equiv.symm_apply_apply]
  have notLive : ¬networkRecords depth <
      priorRequests * nonzeroScalarCount width :=
    Nat.not_lt.mpr priorFits
  unfold greedyStageInputIndex
  simp only [decoded]
  split
  · rename_i live
    exact False.elim (notLive live)
  · apply Fin.ext
    rfl

/-- Decode the point presented to one record of the next scheduler stage. -/
noncomputable def greedyStagePoints
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth priorRequests : Nat)
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (state : Fin (priorRequests * lineBitWidth dimension width +
      pointBitWidth dimension width) -> Bool)
    (record : Fin (networkRecords depth)) :
    Fin dimension -> BinaryExtension width :=
  binaryExtensionVectorCoordinate widthPositive fun bit =>
    (greedyStageInputCircuit dimension width depth priorRequests
      priorFits).eval DeMorgan.interpretation state
        (SchedulerStage.stagePointInputIndex depth
          (pointBitWidth dimension width) record bit)

theorem greedyStageInputCircuit_pointBits
    (widthPositive : 0 < width)
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (state : Fin (priorRequests * lineBitWidth dimension width +
      pointBitWidth dimension width) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin (pointBitWidth dimension width)) :
    (greedyStageInputCircuit dimension width depth priorRequests
        priorFits).eval DeMorgan.interpretation state
        (SchedulerStage.stagePointInputIndex depth
          (pointBitWidth dimension width) record bit) =
      binaryExtensionVectorBits widthPositive
        (greedyStagePoints dimension widthPositive depth priorRequests
          priorFits state record) bit := by
  rw [greedyStagePoints]
  exact (congrFun (binaryExtensionVectorBits_vectorCoordinate
    widthPositive fun localBit =>
      (greedyStageInputCircuit dimension width depth priorRequests
        priorFits).eval DeMorgan.interpretation state
          (SchedulerStage.stagePointInputIndex depth
            (pointBitWidth dimension width) record localBit)) bit).symm

theorem greedyStagePoints_eq_target_of_padding
    (widthPositive : 0 < width)
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (state : Fin (priorRequests * lineBitWidth dimension width +
      pointBitWidth dimension width) -> Bool)
    (target : Fin dimension -> BinaryExtension width)
    (targetBits : ∀ bit,
      state (Fin.natAdd
        (priorRequests * lineBitWidth dimension width) bit) =
        binaryExtensionVectorBits widthPositive target bit)
    (record : Fin (networkRecords depth))
    (padding : ¬record.val <
      priorRequests * nonzeroScalarCount width) :
    greedyStagePoints dimension widthPositive depth priorRequests
        priorFits state record = target := by
  funext coordinate
  rw [← binaryExtensionVectorCoordinate_vectorBits
    widthPositive target coordinate]
  unfold greedyStagePoints binaryExtensionVectorCoordinate
  apply congrArg (encodeBinaryExtension widthPositive)
  funext bit
  rw [greedyStageInputCircuit, Circuit.eval_mapOutputs, Circuit.eval_id]
  change state (greedyStageInputIndex dimension width depth priorRequests
    priorFits (SchedulerStage.stagePointInputIndex depth
      (pointBitWidth dimension width) record
      (finProdFinEquiv (coordinate, bit)))) = _
  rw [greedyStageInputIndex_point_of_padding priorFits record
    (finProdFinEquiv (coordinate, bit)) padding,
    targetBits]

theorem greedyStageInputCircuit_targetBits
    (widthPositive : 0 < width)
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (state : Fin (priorRequests * lineBitWidth dimension width +
      pointBitWidth dimension width) -> Bool)
    (target : Fin dimension -> BinaryExtension width)
    (targetBits : ∀ bit,
      state (Fin.natAdd
        (priorRequests * lineBitWidth dimension width) bit) =
        binaryExtensionVectorBits widthPositive target bit)
    (bit : Fin (pointBitWidth dimension width)) :
    (greedyStageInputCircuit dimension width depth priorRequests
        priorFits).eval DeMorgan.interpretation state
        (SchedulerStage.stageTargetInputIndex depth
          (pointBitWidth dimension width) bit) =
      binaryExtensionVectorBits widthPositive target bit := by
  rw [greedyStageInputCircuit, Circuit.eval_mapOutputs, Circuit.eval_id]
  change state (greedyStageInputIndex dimension width depth priorRequests
    priorFits (SchedulerStage.stageTargetInputIndex depth
      (pointBitWidth dimension width) bit)) = _
  rw [greedyStageInputIndex_target priorFits bit, targetBits]

theorem pointDifferentIndices_greedyStagePoints_card_le
    (widthPositive : 0 < width)
    (priorFits : priorRequests * nonzeroScalarCount width ≤
      networkRecords depth)
    (state : Fin (priorRequests * lineBitWidth dimension width +
      pointBitWidth dimension width) -> Bool)
    (target : Fin dimension -> BinaryExtension width)
    (targetBits : ∀ bit,
      state (Fin.natAdd
        (priorRequests * lineBitWidth dimension width) bit) =
        binaryExtensionVectorBits widthPositive target bit) :
    (SchedulerStage.pointDifferentIndices
      (greedyStagePoints dimension widthPositive depth priorRequests
        priorFits state) target).card ≤
      priorRequests * nonzeroScalarCount width := by
  classical
  let live : Finset (Fin (networkRecords depth)) :=
    Finset.univ.filter fun record =>
      record.val < priorRequests * nonzeroScalarCount width
  have subsetLive : SchedulerStage.pointDifferentIndices
      (greedyStagePoints dimension widthPositive depth priorRequests
        priorFits state) target ⊆ live := by
    intro record recordDifferent
    simp only [SchedulerStage.pointDifferentIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at recordDifferent
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ record, ?_⟩
    by_contra padding
    exact recordDifferent
      (greedyStagePoints_eq_target_of_padding widthPositive priorFits
        state target targetBits record padding)
  calc
    (SchedulerStage.pointDifferentIndices
        (greedyStagePoints dimension widthPositive depth priorRequests
          priorFits state) target).card ≤ live.card :=
      Finset.card_le_card subsetLive
    _ = min (networkRecords depth)
        (priorRequests * nonzeroScalarCount width) := by
      exact Fin.card_filter_val_lt
    _ = priorRequests * nonzeroScalarCount width :=
      min_eq_right priorFits

/-- Recursively unrolled circuit for a fixed request group.  Its output is
the request-major concatenation of all enumerated punctured lines. -/
noncomputable def greedyScheduleCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) :
    (requests : Nat) ->
    (requests * nonzeroScalarCount width ≤ networkRecords depth) ->
    Circuit DeMorgan.signature
      (requests * pointBitWidth dimension width)
      (greedyScheduleGateCount dimension widthPositive depth requests)
      (requests * lineBitWidth dimension width)
  | 0, _ => (Circuit.id DeMorgan.signature 0).castCounts
      (Nat.zero_mul (pointBitWidth dimension width)).symm rfl
      (Nat.zero_mul (lineBitWidth dimension width)).symm
  | requests + 1, allFit => by
      have priorFit : requests * nonzeroScalarCount width ≤
          networkRecords depth := by
        apply le_trans _ allFit
        exact Nat.mul_le_mul_right _ (Nat.le_succ requests)
      let prefixCircuit :=
        (greedyScheduleCircuit dimension widthPositive depth
          requests priorFit).mapInputs
            (targetPrefixInputIndex requests
              (pointBitWidth dimension width))
      let targetCircuit : Circuit DeMorgan.signature
          ((requests + 1) * pointBitWidth dimension width) 0
          (pointBitWidth dimension width) :=
        (Circuit.id DeMorgan.signature
          ((requests + 1) * pointBitWidth dimension width)).mapOutputs
            (currentTargetInputIndex requests
              (pointBitWidth dimension width))
      let retainedState := prefixCircuit.parallel targetCircuit
      let stageInput := greedyStageInputCircuit
        dimension width depth requests priorFit
      let currentLine :=
        (scheduledLineEnumerationCircuit
          dimension widthPositive depth).comp stageInput
      let retainedPrefix : Circuit DeMorgan.signature
          (requests * lineBitWidth dimension width +
            pointBitWidth dimension width)
          0 (requests * lineBitWidth dimension width) :=
        (Circuit.id DeMorgan.signature
          (requests * lineBitWidth dimension width +
            pointBitWidth dimension width)).mapOutputs
              (Fin.castAdd (pointBitWidth dimension width))
      let appendLine := (retainedPrefix.parallel currentLine).castCounts
        rfl rfl (Nat.succ_mul requests
          (lineBitWidth dimension width)).symm
      exact (appendLine.comp retainedState).castCounts rfl
        (by
          simp [greedyScheduleGateCount, Circuit.size]) rfl

/-! ## Decoding the recursively emitted schedule -/

/-- Capacity for a request prefix follows from capacity for one additional
request.  This remains an ordinary proof parameter. -/
theorem priorRequestsFit
    (allFit : (requests + 1) * nonzeroScalarCount width ≤
      networkRecords depth) :
    requests * nonzeroScalarCount width ≤ networkRecords depth := by
  apply le_trans _ allFit
  exact Nat.mul_le_mul_right _ (Nat.le_succ requests)

/-- Evaluate the unrolled scheduler on a row-major target array. -/
noncomputable def greedyScheduleOutput
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth requests : Nat)
    (allFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width) :
    Fin (requests * lineBitWidth dimension width) -> Bool :=
  (greedyScheduleCircuit dimension widthPositive depth requests
    allFit).eval DeMorgan.interpretation
      (targetArrayBits widthPositive targets)

/-- Output bits belonging to one requested line. -/
noncomputable def scheduledLineBits
    (output : Fin (requests * lineBitWidth dimension width) -> Bool)
    (request : Fin requests) :
    Fin (lineBitWidth dimension width) -> Bool :=
  directProductInput output request

/-- Decode one point position of one scheduled line. -/
noncomputable def scheduledLinePoint
    (widthPositive : 0 < width)
    (output : Fin (requests * lineBitWidth dimension width) -> Bool)
    (request : Fin requests)
    (scalar : Fin (nonzeroScalarCount width)) :
    Fin dimension -> BinaryExtension width :=
  binaryExtensionVectorCoordinate widthPositive
    (directProductInput (scheduledLineBits output request) scalar)

/-- Decode the recovery set emitted for one request. -/
noncomputable def scheduledLineSet
    (widthPositive : 0 < width)
    (output : Fin (requests * lineBitWidth dimension width) -> Bool)
    (request : Fin requests) :
    Finset (Fin dimension -> BinaryExtension width) :=
  decodedLineOutputSet widthPositive (scheduledLineBits output request)

/-- An order-oriented formulation of pairwise disjointness, convenient for
the greedy induction. -/
def PairwiseDisjointFamily
    (sets : Fin requests -> Finset pointType) : Prop :=
  ∀ earlier later, earlier < later ->
    Disjoint (sets earlier) (sets later)

theorem PairwiseDisjointFamily.disjoint_of_ne
    {sets : Fin requests -> Finset pointType}
    (pairwise : PairwiseDisjointFamily sets)
    {left right : Fin requests}
    (different : left ≠ right) :
    Disjoint (sets left) (sets right) := by
  rcases lt_or_gt_of_ne different with before | after
  · exact pairwise left right before
  · exact (pairwise right left after).symm

theorem PairwiseDisjointFamily.snoc
    {sets : Fin requests -> Finset pointType}
    {newSet : Finset pointType}
    (pairwise : PairwiseDisjointFamily sets)
    (newDisjoint : ∀ request, Disjoint (sets request) newSet) :
    PairwiseDisjointFamily (Fin.snoc sets newSet) := by
  intro earlier later before
  induction later using Fin.lastCases with
  | last =>
      induction earlier using Fin.lastCases with
      | last => omega
      | cast priorEarlier => simpa using newDisjoint priorEarlier
  | cast priorLater =>
      induction earlier using Fin.lastCases with
      | last =>
          change requests < priorLater.val at before
          omega
      | cast priorEarlier =>
          simpa using pairwise priorEarlier priorLater (by simpa using before)

theorem finAppend_comp_castAdd
    (leftValues : Fin prefixSize -> valueType)
    (rightValues : Fin suffixSize -> valueType) :
    Fin.append leftValues rightValues ∘ Fin.castAdd suffixSize =
      leftValues := by
  funext index
  simp [Function.comp_apply]

/-- One unfolding step of the scheduler evaluation: retain the prefix output,
append the current target, form the next stage input, and append its line. -/
theorem greedyScheduleOutput_succ
    (allFit : (requests + 1) * nonzeroScalarCount width ≤
      networkRecords depth)
    (targets : Fin (requests + 1) ->
      Fin dimension -> BinaryExtension width) :
    greedyScheduleOutput dimension widthPositive depth (requests + 1)
        allFit targets =
      fun output =>
        Fin.append
          (greedyScheduleOutput dimension widthPositive depth requests
            (priorRequestsFit allFit)
            (fun request => targets request.castSucc))
          ((scheduledLineEnumerationCircuit dimension widthPositive depth).eval
            DeMorgan.interpretation
            ((greedyStageInputCircuit dimension width depth requests
              (priorRequestsFit allFit)).eval DeMorgan.interpretation
              (Fin.append
                (greedyScheduleOutput dimension widthPositive depth requests
                  (priorRequestsFit allFit)
                  (fun request => targets request.castSucc))
                (binaryExtensionVectorBits widthPositive
                  (targets (Fin.last requests))))))
          (Fin.cast (Nat.succ_mul requests
            (lineBitWidth dimension width)) output) := by
  funext output
  simp only [greedyScheduleOutput, greedyScheduleCircuit,
    Circuit.eval_castCounts, Fin.cast_refl, Function.comp_id,
    Circuit.eval_comp, Circuit.eval_parallel, Circuit.eval_mapInputs,
    Circuit.eval_mapOutputs, Circuit.eval_id]
  rw [targetArrayBits_prefix, targetArrayBits_current]
  rw [finAppend_comp_castAdd]
  rfl

theorem cast_succ_mul_finProd_castSucc
    (request : Fin requests)
    (bit : Fin blockWidth) :
    Fin.cast (Nat.succ_mul requests blockWidth)
        (finProdFinEquiv (request.castSucc, bit)) =
      Fin.castAdd blockWidth (finProdFinEquiv (request, bit)) := by
  apply Fin.ext
  simp [finProdFinEquiv]

theorem cast_succ_mul_finProd_last
    (bit : Fin blockWidth) :
    Fin.cast (Nat.succ_mul requests blockWidth)
        (finProdFinEquiv (Fin.last requests, bit)) =
      Fin.natAdd (requests * blockWidth) bit := by
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Earlier request blocks are preserved exactly by one recursive stage. -/
theorem scheduledLineBits_greedyScheduleOutput_succ_castSucc
    (allFit : (requests + 1) * nonzeroScalarCount width ≤
      networkRecords depth)
    (targets : Fin (requests + 1) ->
      Fin dimension -> BinaryExtension width)
    (request : Fin requests) :
    scheduledLineBits
        (greedyScheduleOutput dimension widthPositive depth (requests + 1)
          allFit targets) request.castSucc =
      scheduledLineBits
        (greedyScheduleOutput dimension widthPositive depth requests
          (priorRequestsFit allFit)
          (fun prior => targets prior.castSucc)) request := by
  funext bit
  unfold scheduledLineBits directProductInput
  rw [greedyScheduleOutput_succ]
  change Fin.append _ _
    (Fin.cast (Nat.succ_mul requests (lineBitWidth dimension width))
      (finProdFinEquiv (request.castSucc, bit))) = _
  rw [cast_succ_mul_finProd_castSucc, Fin.append_left]

/-- The final request block is exactly the output of the newly evaluated
scheduler-and-enumerator stage. -/
theorem scheduledLineBits_greedyScheduleOutput_succ_last
    (allFit : (requests + 1) * nonzeroScalarCount width ≤
      networkRecords depth)
    (targets : Fin (requests + 1) ->
      Fin dimension -> BinaryExtension width) :
    scheduledLineBits
        (greedyScheduleOutput dimension widthPositive depth (requests + 1)
          allFit targets) (Fin.last requests) =
      (scheduledLineEnumerationCircuit dimension widthPositive depth).eval
        DeMorgan.interpretation
        ((greedyStageInputCircuit dimension width depth requests
          (priorRequestsFit allFit)).eval DeMorgan.interpretation
          (Fin.append
            (greedyScheduleOutput dimension widthPositive depth requests
              (priorRequestsFit allFit)
              (fun prior => targets prior.castSucc))
            (binaryExtensionVectorBits widthPositive
              (targets (Fin.last requests))))) := by
  funext bit
  unfold scheduledLineBits directProductInput
  rw [greedyScheduleOutput_succ]
  change Fin.append _ _
    (Fin.cast (Nat.succ_mul requests (lineBitWidth dimension width))
      (finProdFinEquiv (Fin.last requests, bit))) = _
  rw [cast_succ_mul_finProd_last, Fin.append_right]

/-- Location in the fixed power-of-two stage array of one previously emitted
line point. -/
noncomputable def retainedRecordIndex
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (request : Fin requests)
    (scalar : Fin (nonzeroScalarCount width)) :
    Fin (networkRecords depth) :=
  ⟨(finProdFinEquiv (request, scalar)).val,
    (finProdFinEquiv (request, scalar)).isLt.trans_le priorFit⟩

@[simp] theorem retainedRecordIndex_val
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (request : Fin requests)
    (scalar : Fin (nonzeroScalarCount width)) :
    (retainedRecordIndex priorFit request scalar).val =
      (finProdFinEquiv (request, scalar)).val := rfl

theorem retainedRecordIndex_live
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (request : Fin requests)
    (scalar : Fin (nonzeroScalarCount width)) :
    (retainedRecordIndex priorFit request scalar).val <
      requests * nonzeroScalarCount width :=
  (finProdFinEquiv (request, scalar)).isLt

theorem greedyStageInputIndex_retainedRecord
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (request : Fin requests)
    (scalar : Fin (nonzeroScalarCount width))
    (bit : Fin (pointBitWidth dimension width)) :
    greedyStageInputIndex dimension width depth requests priorFit
        (SchedulerStage.stagePointInputIndex depth
          (pointBitWidth dimension width)
          (retainedRecordIndex priorFit request scalar) bit) =
      Fin.castAdd (pointBitWidth dimension width)
        (finProdFinEquiv (request, finProdFinEquiv (scalar, bit))) := by
  let record := retainedRecordIndex priorFit request scalar
  have decoded :
      (finProdFinEquiv
        (m := networkRecords depth + 1)
        (n := pointBitWidth dimension width)).symm
          (SchedulerStage.stagePointInputIndex depth
            (pointBitWidth dimension width) record bit) =
        (record.castSucc, bit) := by
    have flattened : SchedulerStage.stagePointInputIndex depth
          (pointBitWidth dimension width) record bit =
        finProdFinEquiv (record.castSucc, bit) := by
      apply Fin.ext
      simp [SchedulerStage.stagePointInputIndex, blockPrefixIndex,
        finProdFinEquiv]
    rw [flattened, Equiv.symm_apply_apply]
  have live : record.val < requests * nonzeroScalarCount width :=
    retainedRecordIndex_live priorFit request scalar
  dsimp only [record] at decoded live
  unfold greedyStageInputIndex
  simp only [decoded]
  have liveCast : ↑(retainedRecordIndex priorFit request scalar).castSucc <
      requests * nonzeroScalarCount width := live
  rw [dite_eq_left liveCast]
  apply Fin.ext
  simp [retainedRecordIndex, finProdFinEquiv,
    lineBitWidth, pointBitWidth, Nat.mul_assoc]
  ring

/-- Every previously emitted point is decoded identically when retained as a
live point of the next scheduler stage. -/
theorem greedyStagePoints_retainedRecord
    (widthPositive : 0 < width)
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (prefixOutput :
      Fin (requests * lineBitWidth dimension width) -> Bool)
    (target : Fin dimension -> BinaryExtension width)
    (request : Fin requests)
    (scalar : Fin (nonzeroScalarCount width)) :
    greedyStagePoints dimension widthPositive depth requests priorFit
        (Fin.append prefixOutput
          (binaryExtensionVectorBits widthPositive target))
        (retainedRecordIndex priorFit request scalar) =
      scheduledLinePoint widthPositive prefixOutput request scalar := by
  unfold greedyStagePoints scheduledLinePoint scheduledLineBits
  apply congrArg (binaryExtensionVectorCoordinate widthPositive)
  funext bit
  rw [greedyStageInputCircuit, Circuit.eval_mapOutputs, Circuit.eval_id]
  change Fin.append prefixOutput
      (binaryExtensionVectorBits widthPositive target)
      (greedyStageInputIndex dimension width depth requests priorFit
        (SchedulerStage.stagePointInputIndex depth
          (pointBitWidth dimension width)
          (retainedRecordIndex priorFit request scalar) bit)) =
    prefixOutput
      (finProdFinEquiv (request, finProdFinEquiv (scalar, bit)))
  rw [greedyStageInputIndex_retainedRecord, Fin.append_left]

theorem scheduledLinePoint_mem_greedyStagePointArraySet
    (widthPositive : 0 < width)
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (prefixOutput :
      Fin (requests * lineBitWidth dimension width) -> Bool)
    (target : Fin dimension -> BinaryExtension width)
    (request : Fin requests)
    (scalar : Fin (nonzeroScalarCount width)) :
    scheduledLinePoint widthPositive prefixOutput request scalar ∈
      SchedulerStage.pointArraySet
        (greedyStagePoints dimension widthPositive depth requests priorFit
          (Fin.append prefixOutput
            (binaryExtensionVectorBits widthPositive target))) := by
  classical
  unfold SchedulerStage.pointArraySet
  apply Finset.mem_image.mpr
  refine ⟨retainedRecordIndex priorFit request scalar,
    Finset.mem_univ _, ?_⟩
  exact greedyStagePoints_retainedRecord widthPositive priorFit
    prefixOutput target request scalar

theorem scheduledLineSet_subset_greedyStagePointArraySet
    (widthPositive : 0 < width)
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (prefixOutput :
      Fin (requests * lineBitWidth dimension width) -> Bool)
    (target : Fin dimension -> BinaryExtension width) :
    ∀ request, scheduledLineSet widthPositive prefixOutput request ⊆
      SchedulerStage.pointArraySet
        (greedyStagePoints dimension widthPositive depth requests priorFit
          (Fin.append prefixOutput
            (binaryExtensionVectorBits widthPositive target))) := by
  classical
  intro request point pointMember
  unfold scheduledLineSet decodedLineOutputSet at pointMember
  rw [Finset.mem_image] at pointMember
  obtain ⟨scalar, _, equality⟩ := pointMember
  rw [← equality]
  exact scheduledLinePoint_mem_greedyStagePointArraySet
    widthPositive priorFit prefixOutput target request scalar

theorem pointDifferentIndices_greedyStageOutput_card_le
    (widthPositive : 0 < width)
    (priorFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (prefixOutput :
      Fin (requests * lineBitWidth dimension width) -> Bool)
    (target : Fin dimension -> BinaryExtension width) :
    (SchedulerStage.pointDifferentIndices
      (greedyStagePoints dimension widthPositive depth requests priorFit
        (Fin.append prefixOutput
          (binaryExtensionVectorBits widthPositive target))) target).card ≤
      requests * nonzeroScalarCount width := by
  apply pointDifferentIndices_greedyStagePoints_card_le
    widthPositive priorFit _ target
  intro bit
  rw [Fin.append_right]

/-! ## Correctness of the unrolled greedy scheduler -/

/-- The exact constructive greedy scheduler theorem.  Each request receives
the punctured affine line through its target in an explicitly produced
projective direction, and the emitted recovery sets are pairwise disjoint. -/
theorem greedyScheduleCircuit_correct
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (requests : Nat)
    (allFit : requests * nonzeroScalarCount width ≤
      networkRecords depth)
    (capacity : requests * nonzeroScalarCount width <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)))
    (targets : Fin requests ->
      Fin dimension -> BinaryExtension width) :
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
            allFit targets)) := by
  induction requests with
  | zero =>
      refine ⟨fun request => Fin.elim0 request, ?_, ?_, ?_⟩
      · intro request
        exact Fin.elim0 request
      · intro request
        exact Fin.elim0 request
      · intro earlier
        exact Fin.elim0 earlier
  | succ priorRequests inductionHypothesis =>
      let priorFit := priorRequestsFit allFit
      let priorTargets : Fin priorRequests ->
          Fin dimension -> BinaryExtension width :=
        fun request => targets request.castSucc
      let priorOutput := greedyScheduleOutput dimension widthPositive depth
        priorRequests priorFit priorTargets
      let target := targets (Fin.last priorRequests)
      let stageState := Fin.append priorOutput
        (binaryExtensionVectorBits widthPositive target)
      let points := greedyStagePoints dimension widthPositive depth
        priorRequests priorFit stageState
      let stageInput :=
        (greedyStageInputCircuit dimension width depth priorRequests
          priorFit).eval DeMorgan.interpretation stageState
      let stageOutput :=
        (scheduledLineEnumerationCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation stageInput
      let fullOutput := greedyScheduleOutput dimension widthPositive depth
        (priorRequests + 1) allFit targets
      have priorCapacity :
          priorRequests * nonzeroScalarCount width <
            Nat.card (ℙ (BinaryExtension width)
              (Fin dimension -> BinaryExtension width)) :=
        lt_of_le_of_lt
          (Nat.mul_le_mul_right _ (Nat.le_succ priorRequests)) capacity
      obtain ⟨priorDirections, priorRecordCorrect, priorSetCorrect,
          priorPairwise⟩ :=
        inductionHypothesis priorFit priorCapacity priorTargets
      have stateTargetBits : ∀ bit,
          stageState (Fin.natAdd
            (priorRequests * lineBitWidth dimension width) bit) =
            binaryExtensionVectorBits widthPositive target bit := by
        intro bit
        dsimp only [stageState]
        rw [Fin.append_right]
      have stagePointBits : ∀ record bit,
          stageInput (SchedulerStage.stagePointInputIndex depth
              (pointBitWidth dimension width) record bit) =
            binaryExtensionVectorBits widthPositive (points record) bit := by
        intro record bit
        exact greedyStageInputCircuit_pointBits widthPositive priorFit
          stageState record bit
      have stageTargetBits : ∀ bit,
          stageInput (SchedulerStage.stageTargetInputIndex depth
              (pointBitWidth dimension width) bit) =
            binaryExtensionVectorBits widthPositive target bit := by
        exact greedyStageInputCircuit_targetBits widthPositive priorFit
          stageState target stateTargetBits
      have stageCapacity :
          (SchedulerStage.pointDifferentIndices points target).card <
            Nat.card (ℙ (BinaryExtension width)
              (Fin dimension -> BinaryExtension width)) := by
        calc
          (SchedulerStage.pointDifferentIndices points target).card ≤
              priorRequests * nonzeroScalarCount width := by
            exact pointDifferentIndices_greedyStageOutput_card_le
              widthPositive priorFit priorOutput target
          _ ≤ (priorRequests + 1) * nonzeroScalarCount width :=
            Nat.mul_le_mul_right _ (Nat.le_succ priorRequests)
          _ < Nat.card (ℙ (BinaryExtension width)
              (Fin dimension -> BinaryExtension width)) := capacity
      obtain ⟨newDirection, newRecordCorrect, newSetCorrect,
          newDisjoint⟩ :=
        scheduledLineEnumerationCircuit_sound_input_of_nonzero_capacity
          widthPositive widthAtLeastTwo stageInput points target
          stagePointBits stageTargetBits stageCapacity
      have earlierLineBits : ∀ request : Fin priorRequests,
          scheduledLineBits fullOutput request.castSucc =
            scheduledLineBits priorOutput request := by
        intro request
        exact scheduledLineBits_greedyScheduleOutput_succ_castSucc
          allFit targets request
      have lastLineBits :
          scheduledLineBits fullOutput (Fin.last priorRequests) =
            stageOutput := by
        exact scheduledLineBits_greedyScheduleOutput_succ_last
          allFit targets
      refine ⟨Fin.snoc priorDirections newDirection, ?_, ?_, ?_⟩
      · intro request scalar
        induction request using Fin.lastCases with
        | last =>
            unfold scheduledLinePoint
            rw [lastLineBits, Fin.snoc_last]
            exact newRecordCorrect scalar
        | cast priorRequest =>
            unfold scheduledLinePoint
            rw [earlierLineBits, Fin.snoc_castSucc]
            exact priorRecordCorrect priorRequest scalar
      · intro request
        induction request using Fin.lastCases with
        | last =>
            unfold scheduledLineSet
            rw [lastLineBits, Fin.snoc_last]
            exact newSetCorrect
        | cast priorRequest =>
            unfold scheduledLineSet
            rw [earlierLineBits, Fin.snoc_castSucc]
            exact priorSetCorrect priorRequest
      · have priorSubset : ∀ request,
            scheduledLineSet widthPositive priorOutput request ⊆
              SchedulerStage.pointArraySet points := by
            exact scheduledLineSet_subset_greedyStagePointArraySet
              widthPositive priorFit priorOutput target
        have oldNewDisjoint : ∀ request,
            Disjoint (scheduledLineSet widthPositive priorOutput request)
              (decodedLineOutputSet widthPositive stageOutput) := by
            intro request
            rw [newSetCorrect]
            exact newDisjoint.symm.mono_left (priorSubset request)
        have fullSets :
            scheduledLineSet widthPositive fullOutput =
              Fin.snoc (scheduledLineSet widthPositive priorOutput)
                (decodedLineOutputSet widthPositive stageOutput) := by
            funext request
            induction request using Fin.lastCases with
            | last =>
                rw [Fin.snoc_last]
                unfold scheduledLineSet
                rw [lastLineBits]
            | cast priorRequest =>
                rw [Fin.snoc_castSucc]
                unfold scheduledLineSet
                rw [earlierLineBits]
        rw [fullSets]
        exact priorPairwise.snoc oldNewDisjoint

/-! ## Cost of the unrolled scheduler -/

/-- The recursive scheduler uses one fixed-depth scheduler-and-enumerator
stage per request; all retained-state and target wiring is free. -/
theorem greedyScheduleCircuit_cost
    (widthPositive : 0 < width)
    (requests : Nat)
    (allFit : requests * nonzeroScalarCount width ≤
      networkRecords depth) :
    (greedyScheduleCircuit dimension widthPositive depth requests
      allFit).cost DeMorgan.standardCost =
      requests *
        (scheduledLineEnumerationCircuit dimension widthPositive depth).cost
          DeMorgan.standardCost := by
  induction requests with
  | zero => simp [greedyScheduleCircuit]
  | succ priorRequests inductionHypothesis =>
      rw [greedyScheduleCircuit]
      simp only [Circuit.cost_castCounts, Circuit.cost_comp,
        Circuit.cost_parallel, Circuit.cost_mapInputs,
        Circuit.cost_mapOutputs, Circuit.cost_id,
        greedyStageInputCircuit_cost]
      rw [inductionHypothesis]
      ring

/-- Explicit finite cost bound corresponding to the manuscript's
`g` stages, each provisioned for `g (q - 1)` retained points. -/
theorem greedyScheduleCircuit_cost_le
    (widthPositive : 0 < width)
    (requests : Nat)
    (allFit : requests * nonzeroScalarCount width ≤
      networkRecords depth) :
    (greedyScheduleCircuit dimension widthPositive depth requests
      allFit).cost DeMorgan.standardCost ≤
      requests * scheduledLineEnumerationCostBound dimension width depth := by
  rw [greedyScheduleCircuit_cost widthPositive requests allFit]
  exact Nat.mul_le_mul_left requests
    (scheduledLineEnumerationCircuit_cost_le
      (dimension := dimension) (depth := depth) widthPositive)

end SchedulerIteration
end MassProduction
end Algebraic
