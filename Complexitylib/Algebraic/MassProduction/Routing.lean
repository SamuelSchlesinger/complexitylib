/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingBy

/-!
# Fixed-wire record routing primitives

After records are sorted by `(key, type)`, both scatter and gather use the
same local operation: a destination record copies the payload of its immediate
predecessor exactly when the predecessor has the source tag and the keys
agree.  The first array position uses a fixed dummy payload.  This module
builds that operation as an explicit De Morgan circuit and proves its exact
semantics and a polynomial cost bound.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Routing

open scoped BigOperators
open Sorting

/-- Width of a record containing key bits, one type bit, and payload bits. -/
def recordWidth (keyWidth payloadWidth : Nat) : Nat :=
  keyWidth + 1 + payloadWidth

/-- Flat row-major index of one bit in a routing record array. -/
def recordBitIndex
    (depth keyWidth payloadWidth : Nat)
    (record : Fin (networkRecords depth))
    (bit : Fin (recordWidth keyWidth payloadWidth)) :
    Fin (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  finProdFinEquiv (record, bit)

@[simp] theorem finProdFinEquiv_symm_recordBitIndex
    (record : Fin (networkRecords depth))
    (bit : Fin (recordWidth keyWidth payloadWidth)) :
    (finProdFinEquiv.symm
      (recordBitIndex depth keyWidth payloadWidth record bit)) =
        (record, bit) := by
  unfold recordBitIndex
  exact Equiv.symm_apply_apply finProdFinEquiv (record, bit)

/-- Index of one key bit in a routing record. -/
def keyBit
    (keyWidth payloadWidth : Nat)
    (bit : Fin keyWidth) : Fin (recordWidth keyWidth payloadWidth) :=
  ⟨bit.val, by unfold recordWidth; omega⟩

/-- Index of the source/destination type bit. -/
def tagBit
    (keyWidth payloadWidth : Nat) :
    Fin (recordWidth keyWidth payloadWidth) :=
  ⟨keyWidth, by unfold recordWidth; omega⟩

/-- Index of one payload bit in a routing record. -/
def payloadBit
    (keyWidth payloadWidth : Nat)
    (bit : Fin payloadWidth) : Fin (recordWidth keyWidth payloadWidth) :=
  ⟨keyWidth + 1 + bit.val, by unfold recordWidth; omega⟩

/-- Key projection from one standalone packed record. -/
def packedRecordKey
    (record : Fin (recordWidth keyWidth payloadWidth) -> Bool) :
    Fin keyWidth -> Bool :=
  fun bit => record (keyBit keyWidth payloadWidth bit)

/-- Type tag from one standalone packed record. -/
def packedRecordTag
    (record : Fin (recordWidth keyWidth payloadWidth) -> Bool) : Bool :=
  record (tagBit keyWidth payloadWidth)

/-- Payload projection from one standalone packed record. -/
def packedRecordPayload
    (record : Fin (recordWidth keyWidth payloadWidth) -> Bool) :
    Fin payloadWidth -> Bool :=
  fun bit => record (payloadBit keyWidth payloadWidth bit)

/-- Key projection from one record in a flat routing array. -/
def recordKey
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) ->
      Bool)
    (record : Fin (networkRecords depth)) : Fin keyWidth -> Bool :=
  fun bit => input (recordBitIndex depth keyWidth payloadWidth record
    (keyBit keyWidth payloadWidth bit))

/-- Type tag of one record in a flat routing array. -/
def recordTag
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) ->
      Bool)
    (record : Fin (networkRecords depth)) : Bool :=
  input (recordBitIndex depth keyWidth payloadWidth record
    (tagBit keyWidth payloadWidth))

/-- Payload projection from one record in a flat routing array. -/
def recordPayload
    (input : Fin (networkBits depth (recordWidth keyWidth payloadWidth)) ->
      Bool)
    (record : Fin (networkRecords depth)) : Fin payloadWidth -> Bool :=
  fun bit => input (recordBitIndex depth keyWidth payloadWidth record
    (payloadBit keyWidth payloadWidth bit))

@[simp] theorem packedRecordKey_flatRecords
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    packedRecordKey (flatRecords input record) = recordKey input record := by
  rfl

@[simp] theorem packedRecordTag_flatRecords
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    packedRecordTag (flatRecords input record) = recordTag input record := by
  rfl

@[simp] theorem packedRecordPayload_flatRecords
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    packedRecordPayload (flatRecords input record) =
      recordPayload input record := by
  rfl

/-- The record immediately before a positive array position. -/
def predecessor
    (record : Fin (networkRecords depth))
    (positive : 0 < record.val) : Fin (networkRecords depth) :=
  ⟨record.val - 1, by omega⟩

/-- XNOR of two selected array inputs. -/
def bitEqualExpression
    (left right : Fin n) : DeMorgan.Expression n :=
  .or (.and (.input left) (.input right))
    (.and (.not (.input left)) (.not (.input right)))

@[simp] theorem bitEqualExpression_eval_eq_true_iff
    (left right : Fin n)
    (input : Fin n -> Bool) :
    (bitEqualExpression left right).eval input = true ↔
      input left = input right := by
  generalize leftEquality : input left = leftValue
  generalize rightEquality : input right = rightValue
  cases leftValue <;> cases rightValue <;>
    simp [bitEqualExpression, DeMorgan.Expression.eval,
      leftEquality, rightEquality]

@[simp] theorem bitEqualExpression_standardCost
    (left right : Fin n) :
    (bitEqualExpression left right).standardCost = 5 :=
  rfl

/-- Test one selected input bit against a hardwired Boolean tag. -/
def bitEqualsConstantExpression
    (expected : Bool)
    (input : Fin n) : DeMorgan.Expression n :=
  if expected then .input input else .not (.input input)

@[simp] theorem bitEqualsConstantExpression_eval_eq_true_iff
    (expected : Bool)
    (index : Fin n)
    (input : Fin n -> Bool) :
    (bitEqualsConstantExpression expected index).eval input = true ↔
      input index = expected := by
  cases expected <;> cases valueEquality : input index <;>
    simp [bitEqualsConstantExpression, DeMorgan.Expression.eval,
      valueEquality]

theorem bitEqualsConstantExpression_standardCost_le
    (expected : Bool)
    (index : Fin n) :
    (bitEqualsConstantExpression expected index).standardCost <= 1 := by
  cases expected <;>
    simp [bitEqualsConstantExpression, DeMorgan.Expression.standardCost]

/-- Equality test for the keys of two records. -/
def recordKeysEqualExpression
    (depth keyWidth payloadWidth : Nat)
    (left right : Fin (networkRecords depth)) :
    DeMorgan.Expression
      (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  DeMorgan.Expression.finAnd keyWidth fun bit =>
    bitEqualExpression
      (recordBitIndex depth keyWidth payloadWidth left
        (keyBit keyWidth payloadWidth bit))
      (recordBitIndex depth keyWidth payloadWidth right
        (keyBit keyWidth payloadWidth bit))

theorem recordKeysEqualExpression_eval_eq_true_iff
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (left right : Fin (networkRecords depth)) :
    (recordKeysEqualExpression depth keyWidth payloadWidth left right).eval
        input = true ↔
      recordKey input left = recordKey input right := by
  rw [recordKeysEqualExpression, DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · intro equalBits
    funext bit
    exact (bitEqualExpression_eval_eq_true_iff _ _ input).mp
      (equalBits bit)
  · intro equalKeys bit
    apply (bitEqualExpression_eval_eq_true_iff _ _ input).mpr
    exact congrFun equalKeys bit

@[simp] theorem recordKeysEqualExpression_standardCost
    (left right : Fin (networkRecords depth)) :
    (recordKeysEqualExpression depth keyWidth payloadWidth left right).standardCost =
      6 * keyWidth := by
  rw [recordKeysEqualExpression,
    DeMorgan.Expression.finAnd_standardCost]
  simp only [bitEqualExpression_standardCost, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  omega

/-- Guard saying that `current` is a destination immediately preceded by a
same-key source record. -/
def predecessorMatchExpression
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val) :
    DeMorgan.Expression
      (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  let previous := predecessor current positive
  .and (recordKeysEqualExpression depth keyWidth payloadWidth
      previous current)
    (.and
      (bitEqualsConstantExpression sourceTag
        (recordBitIndex depth keyWidth payloadWidth previous
          (tagBit keyWidth payloadWidth)))
      (bitEqualsConstantExpression destinationTag
        (recordBitIndex depth keyWidth payloadWidth current
          (tagBit keyWidth payloadWidth))))

theorem predecessorMatchExpression_eval_eq_true_iff
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val) :
    (predecessorMatchExpression depth keyWidth payloadWidth
        sourceTag destinationTag current positive).eval input = true ↔
      recordKey input (predecessor current positive) =
          recordKey input current ∧
        recordTag input (predecessor current positive) = sourceTag ∧
        recordTag input current = destinationTag := by
  unfold predecessorMatchExpression
  simp only [DeMorgan.Expression.eval, Bool.and_eq_true,
    recordKeysEqualExpression_eval_eq_true_iff,
    bitEqualsConstantExpression_eval_eq_true_iff]
  rfl

theorem predecessorMatchExpression_standardCost_le
    (sourceTag destinationTag : Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val) :
    (predecessorMatchExpression depth keyWidth payloadWidth
        sourceTag destinationTag current positive).standardCost <=
      6 * keyWidth + 4 := by
  unfold predecessorMatchExpression
  simp only [DeMorgan.Expression.standardCost]
  rw [recordKeysEqualExpression_standardCost]
  have sourceBound := bitEqualsConstantExpression_standardCost_le
    sourceTag (recordBitIndex depth keyWidth payloadWidth
      (predecessor current positive) (tagBit keyWidth payloadWidth))
  have destinationBound := bitEqualsConstantExpression_standardCost_le
    destinationTag (recordBitIndex depth keyWidth payloadWidth
      current (tagBit keyWidth payloadWidth))
  omega

/-- One output bit of a guarded predecessor-copy pass.  Keys and tags are
preserved. Payload bits of a matched destination copy the predecessor;
otherwise payload is the fixed dummy value `false`. -/
def predecessorCopyOutputExpression
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool)
    (output : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth))) :
    DeMorgan.Expression
      (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  let recordAndBit :=
    (finProdFinEquiv
      (m := networkRecords depth)
      (n := recordWidth keyWidth payloadWidth)).symm output
  if payload : keyWidth + 1 <= recordAndBit.2.val then
    if positive : 0 < recordAndBit.1.val then
      let payloadIndex : Fin payloadWidth :=
        ⟨recordAndBit.2.val - (keyWidth + 1), by
          have bound := recordAndBit.2.isLt
          unfold recordWidth at bound
          omega⟩
      Sorting.muxExpression
        (predecessorMatchExpression depth keyWidth payloadWidth
          sourceTag destinationTag recordAndBit.1 positive)
        (.input (recordBitIndex depth keyWidth payloadWidth
          (predecessor recordAndBit.1 positive)
          (payloadBit keyWidth payloadWidth payloadIndex)))
        (.constant false)
    else .constant false
  else .input output

/-- Semantic guarded predecessor-copy pass. -/
def predecessorCopyBits
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    Fin (networkBits depth (recordWidth keyWidth payloadWidth)) -> Bool :=
  fun output =>
    (predecessorCopyOutputExpression depth keyWidth payloadWidth
      sourceTag destinationTag output).eval input

/-- Gate count emitted for one output formula. -/
@[reducible] def predecessorCopyOutputGateCount
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool)
    (output : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth))) : Nat :=
  (predecessorCopyOutputExpression depth keyWidth payloadWidth
    sourceTag destinationTag output).gateCount

/-- Explicit circuit implementing one complete predecessor-copy pass. -/
def predecessorCopyCircuit
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool) :
    Circuit DeMorgan.signature
      (networkBits depth (recordWidth keyWidth payloadWidth))
      (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  Circuit.parallelFin
    (networkBits depth (recordWidth keyWidth payloadWidth)) fun output =>
      (predecessorCopyOutputExpression depth keyWidth payloadWidth
        sourceTag destinationTag output).circuit

@[simp] theorem predecessorCopyCircuit_size
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool) :
    (predecessorCopyCircuit depth keyWidth payloadWidth
        sourceTag destinationTag).size =
      ∑ output, predecessorCopyOutputGateCount depth keyWidth payloadWidth
        sourceTag destinationTag output := by
  simp [predecessorCopyCircuit, predecessorCopyOutputGateCount]

@[simp] theorem predecessorCopyCircuit_eval
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    (predecessorCopyCircuit depth keyWidth payloadWidth
        sourceTag destinationTag).eval DeMorgan.interpretation input =
      predecessorCopyBits depth keyWidth payloadWidth
        sourceTag destinationTag input := by
  funext output
  rw [predecessorCopyCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  rfl

/-- A predecessor-copy pass preserves every key bit. -/
@[simp] theorem predecessorCopyBits_recordKey
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordKey
        (predecessorCopyBits depth keyWidth payloadWidth
          sourceTag destinationTag input) record =
      recordKey input record := by
  funext bit
  unfold networkBits at input
  unfold recordKey predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [networkBits, recordBitIndex, Equiv.symm_apply_apply]
  have notPayload :
      ¬ keyWidth + 1 <= (keyBit keyWidth payloadWidth bit).val := by
    change ¬ keyWidth + 1 <= bit.val
    omega
  rw [dite_eq_right notPayload]
  rfl

/-- A predecessor-copy pass preserves every type tag. -/
@[simp] theorem predecessorCopyBits_recordTag
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordTag
        (predecessorCopyBits depth keyWidth payloadWidth
          sourceTag destinationTag input) record =
      recordTag input record := by
  unfold networkBits at input
  unfold recordTag predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [networkBits, recordBitIndex, Equiv.symm_apply_apply]
  have notPayload :
      ¬ keyWidth + 1 <= (tagBit keyWidth payloadWidth).val := by
    change ¬ keyWidth + 1 <= keyWidth
    omega
  rw [dite_eq_right notPayload]
  rfl

/-- At a positive position, every payload bit is selected by the same
same-key/source/destination guard. -/
theorem predecessorCopyBits_recordPayload_of_positive
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val) :
    recordPayload
        (predecessorCopyBits depth keyWidth payloadWidth
          sourceTag destinationTag input) current =
      if (predecessorMatchExpression depth keyWidth payloadWidth
          sourceTag destinationTag current positive).eval input then
        recordPayload input (predecessor current positive)
      else fun _ => false := by
  funext bit
  unfold recordPayload predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [finProdFinEquiv_symm_recordBitIndex]
  have payload :
      keyWidth + 1 <= (payloadBit keyWidth payloadWidth bit).val := by
    change keyWidth + 1 <= keyWidth + 1 + bit.val
    omega
  rw [dite_eq_left payload, dite_eq_left positive]
  have payloadIndexEquality :
      (⟨(payloadBit keyWidth payloadWidth bit).val - (keyWidth + 1), by
          have bound := (payloadBit keyWidth payloadWidth bit).isLt
          unfold recordWidth at bound
          omega⟩ : Fin payloadWidth) = bit := by
    apply Fin.ext
    change (keyWidth + 1 + bit.val) - (keyWidth + 1) = bit.val
    omega
  rw [payloadIndexEquality]
  rw [Sorting.muxExpression_eval]
  by_cases guardTrue :
      (predecessorMatchExpression depth keyWidth payloadWidth
        sourceTag destinationTag current positive).eval input = true <;>
    simp [guardTrue, DeMorgan.Expression.eval]

/-- The first record has no predecessor and receives the fixed dummy
payload. -/
theorem predecessorCopyBits_recordPayload_zero
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (current : Fin (networkRecords depth))
    (atZero : current.val = 0) :
    recordPayload
        (predecessorCopyBits depth keyWidth payloadWidth
          sourceTag destinationTag input) current =
      fun _ => false := by
  funext bit
  unfold recordPayload predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [finProdFinEquiv_symm_recordBitIndex]
  have payload :
      keyWidth + 1 <= (payloadBit keyWidth payloadWidth bit).val := by
    change keyWidth + 1 <= keyWidth + 1 + bit.val
    omega
  have notPositive : ¬0 < current.val := by omega
  rw [dite_eq_left payload, dite_eq_right notPositive]
  rfl

/-- A correctly tagged same-key predecessor is copied exactly. -/
theorem predecessorCopyBits_recordPayload_of_match
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val)
    (sameKey : recordKey input (predecessor current positive) =
      recordKey input current)
    (previousTag : recordTag input (predecessor current positive) = sourceTag)
    (currentTag : recordTag input current = destinationTag) :
    recordPayload
        (predecessorCopyBits depth keyWidth payloadWidth
          sourceTag destinationTag input) current =
      recordPayload input (predecessor current positive) := by
  rw [predecessorCopyBits_recordPayload_of_positive
    sourceTag destinationTag input current positive]
  have matched :
      (predecessorMatchExpression depth keyWidth payloadWidth
        sourceTag destinationTag current positive).eval input = true :=
    (predecessorMatchExpression_eval_eq_true_iff
      sourceTag destinationTag input current positive).mpr
        ⟨sameKey, previousTag, currentTag⟩
  rw [matched]
  rfl

/-- If the predecessor match condition fails, the destination receives the
fixed dummy payload. -/
theorem predecessorCopyBits_recordPayload_of_no_match
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val)
    (notMatch : ¬(recordKey input (predecessor current positive) =
        recordKey input current ∧
      recordTag input (predecessor current positive) = sourceTag ∧
      recordTag input current = destinationTag)) :
    recordPayload
        (predecessorCopyBits depth keyWidth payloadWidth
          sourceTag destinationTag input) current =
      fun _ => false := by
  rw [predecessorCopyBits_recordPayload_of_positive
    sourceTag destinationTag input current positive]
  have notTrue :
      (predecessorMatchExpression depth keyWidth payloadWidth
        sourceTag destinationTag current positive).eval input ≠ true := by
    intro matched
    exact notMatch
      ((predecessorMatchExpression_eval_eq_true_iff
        sourceTag destinationTag input current positive).mp matched)
  have falseValue :
      (predecessorMatchExpression depth keyWidth payloadWidth
        sourceTag destinationTag current positive).eval input = false := by
    cases valueEquality :
        (predecessorMatchExpression depth keyWidth payloadWidth
          sourceTag destinationTag current positive).eval input
    · rfl
    · exact False.elim (notTrue valueEquality)
  rw [falseValue]
  rfl

theorem predecessorCopyOutputExpression_standardCost_le
    (sourceTag destinationTag : Bool)
    (output : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth))) :
    (predecessorCopyOutputExpression depth keyWidth payloadWidth
        sourceTag destinationTag output).standardCost <=
      12 * keyWidth + 12 := by
  unfold predecessorCopyOutputExpression
  dsimp only
  split_ifs with payload positive
  · rw [Sorting.muxExpression_standardCost]
    simp only [DeMorgan.Expression.standardCost, Nat.add_zero]
    have guardBound := predecessorMatchExpression_standardCost_le
      (depth := depth) (keyWidth := keyWidth)
      (payloadWidth := payloadWidth) sourceTag destinationTag _ positive
    omega
  · simp [DeMorgan.Expression.standardCost]
  · simp [DeMorgan.Expression.standardCost]

/-- One pass has linear record-array size and linear dependence on key width. -/
theorem predecessorCopyCircuit_cost_le
    (sourceTag destinationTag : Bool) :
    (predecessorCopyCircuit depth keyWidth payloadWidth
        sourceTag destinationTag).cost DeMorgan.standardCost <=
      networkBits depth (recordWidth keyWidth payloadWidth) *
        (12 * keyWidth + 12) := by
  rw [predecessorCopyCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    ∑ output : Fin (networkBits depth
          (recordWidth keyWidth payloadWidth)),
        (predecessorCopyOutputExpression depth keyWidth payloadWidth
          sourceTag destinationTag output).standardCost <=
      ∑ _output : Fin (networkBits depth
          (recordWidth keyWidth payloadWidth)),
        (12 * keyWidth + 12) := by
      exact Finset.sum_le_sum fun output _ =>
        predecessorCopyOutputExpression_standardCost_le
          sourceTag destinationTag output
    _ = networkBits depth (recordWidth keyWidth payloadWidth) *
        (12 * keyWidth + 12) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]

/-- The key together with its following tag fits in a routing record. -/
theorem keyAndTagFitsRecord
    (keyWidth payloadWidth : Nat) :
    keyWidth + 1 <= recordWidth keyWidth payloadWidth := by
  unfold recordWidth
  omega

/-- Gate count of a complete sort-then-predecessor-match pass. -/
@[reducible] def sortedPredecessorCopyGateCount
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool) : Nat :=
  Sorting.bitonicSortGateCount
      (keyAndTagFitsRecord keyWidth payloadWidth) depth +
    ∑ output, predecessorCopyOutputGateCount depth keyWidth payloadWidth
      sourceTag destinationTag output

/-- One complete scatter-match or gather-match pass: sort by `(key, tag)`
and perform the guarded predecessor copy. -/
def sortedPredecessorCopyCircuit
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool) :
    Circuit DeMorgan.signature
      (networkBits depth (recordWidth keyWidth payloadWidth))
      (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  (predecessorCopyCircuit depth keyWidth payloadWidth
      sourceTag destinationTag).comp
    (Sorting.bitonicSortCircuit
      (keyAndTagFitsRecord keyWidth payloadWidth) depth true)

@[simp] theorem sortedPredecessorCopyCircuit_size
    (depth keyWidth payloadWidth : Nat)
    (sourceTag destinationTag : Bool) :
    (sortedPredecessorCopyCircuit depth keyWidth payloadWidth
        sourceTag destinationTag).size =
      sortedPredecessorCopyGateCount depth keyWidth payloadWidth
        sourceTag destinationTag := by
  simp [sortedPredecessorCopyCircuit, sortedPredecessorCopyGateCount]

/-- Direction-parameterized match pass.  Descending order with source tag
`true` and destination tag `false` is useful when a subsequent canonical sort
must place destination records first without negating the tag bit. -/
def sortedPredecessorCopyCircuitOrdered
    (depth keyWidth payloadWidth : Nat)
    (ascending sourceTag destinationTag : Bool) :
    Circuit DeMorgan.signature
      (networkBits depth (recordWidth keyWidth payloadWidth))
      (networkBits depth (recordWidth keyWidth payloadWidth)) :=
  (predecessorCopyCircuit depth keyWidth payloadWidth
      sourceTag destinationTag).comp
    (Sorting.bitonicSortCircuit
      (keyAndTagFitsRecord keyWidth payloadWidth) depth ascending)

@[simp] theorem sortedPredecessorCopyCircuitOrdered_size
    (depth keyWidth payloadWidth : Nat)
    (ascending sourceTag destinationTag : Bool) :
    (sortedPredecessorCopyCircuitOrdered depth keyWidth payloadWidth ascending sourceTag destinationTag).size =
      sortedPredecessorCopyGateCount depth keyWidth payloadWidth sourceTag destinationTag := by
  simp [sortedPredecessorCopyCircuitOrdered, sortedPredecessorCopyGateCount]

@[simp] theorem sortedPredecessorCopyCircuitOrdered_eval
    (ascending sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    (sortedPredecessorCopyCircuitOrdered depth keyWidth payloadWidth
        ascending sourceTag destinationTag).eval
        DeMorgan.interpretation input =
      predecessorCopyBits depth keyWidth payloadWidth
        sourceTag destinationTag
        (Sorting.bitonicSortBits
          (keyAndTagFitsRecord keyWidth payloadWidth) depth ascending
          input) := by
  rw [sortedPredecessorCopyCircuitOrdered, Circuit.eval_comp,
    predecessorCopyCircuit_eval, Sorting.bitonicSortCircuit_eval]

@[simp] theorem sortedPredecessorCopyCircuit_eval
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    (sortedPredecessorCopyCircuit depth keyWidth payloadWidth
        sourceTag destinationTag).eval DeMorgan.interpretation input =
      predecessorCopyBits depth keyWidth payloadWidth
        sourceTag destinationTag
        (Sorting.bitonicSortBits
          (keyAndTagFitsRecord keyWidth payloadWidth) depth true input) := by
  rw [sortedPredecessorCopyCircuit, Circuit.eval_comp,
    predecessorCopyCircuit_eval, Sorting.bitonicSortCircuit_eval]

/-- The sorting half of a match pass preserves every complete routing
record before the local payload update. -/
theorem sortedPredecessorCopy_sort_recordsPermute
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool) :
    Sorting.FlatRecordsPermute
      (Sorting.bitonicSortBits
        (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
      input := by
  exact Sorting.bitonicSortBits_recordsPermute
    (keyAndTagFitsRecord keyWidth payloadWidth) depth true input

/-- Explicit cost ledger for one complete sort-and-match pass. -/
theorem sortedPredecessorCopyCircuit_cost_le
    (sourceTag destinationTag : Bool) :
    (sortedPredecessorCopyCircuit depth keyWidth payloadWidth
        sourceTag destinationTag).cost DeMorgan.standardCost <=
      depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth payloadWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkBits depth (recordWidth keyWidth payloadWidth) *
          (12 * keyWidth + 12) := by
  rw [sortedPredecessorCopyCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (Sorting.bitonicSortCircuit_cost_le
      (keyAndTagFitsRecord keyWidth payloadWidth) depth true)
    (predecessorCopyCircuit_cost_le
      (depth := depth) (keyWidth := keyWidth)
      (payloadWidth := payloadWidth) sourceTag destinationTag)

/-- The direction-parameterized pass has the same cost ledger. -/
theorem sortedPredecessorCopyCircuitOrdered_cost_le
    (ascending sourceTag destinationTag : Bool) :
    (sortedPredecessorCopyCircuitOrdered depth keyWidth payloadWidth
        ascending sourceTag destinationTag).cost DeMorgan.standardCost <=
      depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth payloadWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkBits depth (recordWidth keyWidth payloadWidth) *
          (12 * keyWidth + 12) := by
  rw [sortedPredecessorCopyCircuitOrdered, Circuit.cost_comp]
  exact Nat.add_le_add
    (Sorting.bitonicSortCircuit_cost_le
      (keyAndTagFitsRecord keyWidth payloadWidth) depth ascending)
    (predecessorCopyCircuit_cost_le
      (depth := depth) (keyWidth := keyWidth)
      (payloadWidth := payloadWidth) sourceTag destinationTag)

end Routing
end MassProduction
end Algebraic
