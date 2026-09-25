/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingCorrectness

/-!
# Sorting packed records by selected fields

The routing construction uses one physical record layout but sorts the same
records by several different tuples of fields.  Since input and output wiring
is free in the circuit model, a within-record bit permutation turns any such
tuple into the prefix consumed by the verified Batcher sorter.  This module
builds that wrapper and proves that it sorts the selected key, preserves every
complete physical record, and has exactly the cost of the underlying sorter.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting

open Semantics

theorem networkBits_eq_product (depth recordWidth : Nat) :
    networkBits depth recordWidth = networkRecords depth * recordWidth :=
  rfl

/-- Apply the same within-record bit permutation to every record in a flat
row-major array.  The permutation maps a virtual bit position to its physical
position in the record. -/
def recordBitEquiv
    (depth recordWidth : Nat)
    (bitOrder : Equiv.Perm (Fin recordWidth)) :
    Fin (networkBits depth recordWidth) ->
      Fin (networkBits depth recordWidth) :=
  fun flatBit =>
    let recordAndBit :=
      (finProdFinEquiv
        (m := networkRecords depth) (n := recordWidth)).symm
        (Fin.cast (networkBits_eq_product depth recordWidth) flatBit)
    Fin.cast (networkBits_eq_product depth recordWidth).symm
      (finProdFinEquiv (recordAndBit.1, bitOrder recordAndBit.2))

@[simp] theorem recordBitEquiv_recordBit
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (record : Fin (networkRecords depth))
    (bit : Fin recordWidth) :
    recordBitEquiv depth recordWidth bitOrder
        (finProdFinEquiv (record, bit)) =
      finProdFinEquiv (record, bitOrder bit) := by
  apply Fin.ext
  simp [recordBitEquiv, networkBits_eq_product]

/-- Reinterpret each physical record according to `bitOrder`. -/
def reindexRecordBits
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    Fin (networkBits depth recordWidth) -> Bool :=
  input ∘ recordBitEquiv depth recordWidth bitOrder

@[simp] theorem reindexRecordBits_apply_recordBit
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (input : Fin (networkBits depth recordWidth) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin recordWidth) :
    reindexRecordBits bitOrder input (finProdFinEquiv (record, bit)) =
      input (finProdFinEquiv (record, bitOrder bit)) := by
  unfold reindexRecordBits
  change input
    (recordBitEquiv depth recordWidth bitOrder
      (finProdFinEquiv (record, bit))) = _
  rw [recordBitEquiv_recordBit]

@[simp] theorem reindexRecordBits_symm_left
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    reindexRecordBits bitOrder.symm (reindexRecordBits bitOrder input) =
      input := by
  funext flatBit
  let recordAndBit :=
    (finProdFinEquiv
      (m := networkRecords depth) (n := recordWidth)).symm flatBit
  have flatBitEquality :
      flatBit = finProdFinEquiv (recordAndBit.1, recordAndBit.2) := by
    exact ((finProdFinEquiv
      (m := networkRecords depth) (n := recordWidth)).apply_symm_apply
        flatBit).symm
  rw [flatBitEquality]
  simp only [reindexRecordBits_apply_recordBit, Equiv.apply_symm_apply]

@[simp] theorem reindexRecordBits_symm_right
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    reindexRecordBits bitOrder (reindexRecordBits bitOrder.symm input) =
      input := by
  simpa using reindexRecordBits_symm_left bitOrder.symm input

theorem flatRecords_reindexRecordBits
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    flatRecords (reindexRecordBits bitOrder input) =
      fun record bit => flatRecords input record (bitOrder bit) := by
  funext record bit
  unfold flatRecords networkRecord
  exact reindexRecordBits_apply_recordBit bitOrder input record bit

/-- Reindexing every record by the same bit permutation preserves a
record-level permutation relation. -/
theorem FlatRecordsPermute.reindexRecordBits
    (bitOrder : Equiv.Perm (Fin recordWidth))
    {output input : Fin (networkBits depth recordWidth) -> Bool}
    (recordsPermute : FlatRecordsPermute output input) :
    FlatRecordsPermute
      (reindexRecordBits bitOrder output)
      (reindexRecordBits bitOrder input) := by
  unfold FlatRecordsPermute SequencePermutes at recordsPermute ⊢
  rw [flatRecords_reindexRecordBits, flatRecords_reindexRecordBits]
  let reindexRecord : (Fin recordWidth -> Bool) ->
      (Fin recordWidth -> Bool) := fun record bit => record (bitOrder bit)
  change
    (List.ofFn (fun record => reindexRecord (flatRecords output record))).Perm
      (List.ofFn (fun record => reindexRecord (flatRecords input record)))
  have outputEquality :
      List.ofFn (fun record => reindexRecord (flatRecords output record)) =
        List.map reindexRecord (List.ofFn (flatRecords output)) :=
    List.ofFn_comp' (flatRecords output) reindexRecord
  have inputEquality :
      List.ofFn (fun record => reindexRecord (flatRecords input record)) =
        List.map reindexRecord (List.ofFn (flatRecords input)) :=
    List.ofFn_comp' (flatRecords input) reindexRecord
  rw [outputEquality, inputEquality]
  exact recordsPermute.map reindexRecord

/-- Semantic sort by the first `keyWidth` virtual bits selected by
`bitOrder`, returning records in their original physical layout. -/
def bitonicSortByBits
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    Fin (networkBits depth recordWidth) -> Bool :=
  reindexRecordBits bitOrder.symm
    (bitonicSortBits keyFits depth ascending
      (reindexRecordBits bitOrder input))

/-- Explicit Batcher circuit sorting by an arbitrary fixed tuple of record
bits.  Both layout conversions are free wire permutations. -/
def bitonicSortByCircuit
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool) :
    Circuit DeMorgan.signature (networkBits depth recordWidth)
      (networkBits depth recordWidth) :=
  ((bitonicSortCircuit keyFits depth ascending).mapInputs
      (recordBitEquiv depth recordWidth bitOrder)).mapOutputs
    (recordBitEquiv depth recordWidth bitOrder.symm)

@[simp] theorem bitonicSortByCircuit_size
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool) :
    (bitonicSortByCircuit bitOrder keyFits depth ascending).size =
      bitonicSortGateCount keyFits depth := by
  simp [bitonicSortByCircuit]

@[simp] theorem bitonicSortByCircuit_eval
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    (bitonicSortByCircuit bitOrder keyFits depth ascending).eval
        DeMorgan.interpretation input =
      bitonicSortByBits bitOrder keyFits depth ascending input := by
  rw [bitonicSortByCircuit, Circuit.eval_mapOutputs,
    Circuit.eval_mapInputs, bitonicSortCircuit_eval]
  rfl

/-- The selected virtual prefix is sorted in the requested direction. -/
def FlatKeysSortedBy
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) : Prop :=
  FlatKeysSorted keyFits ascending (reindexRecordBits bitOrder input)

theorem bitonicSortByBits_keysSorted
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatKeysSortedBy bitOrder keyFits ascending
      (bitonicSortByBits bitOrder keyFits depth ascending input) := by
  unfold FlatKeysSortedBy bitonicSortByBits
  rw [reindexRecordBits_symm_right]
  exact bitonicSortBits_keysSorted keyFits depth ascending
    (reindexRecordBits bitOrder input)

theorem bitonicSortByBits_recordsPermute
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatRecordsPermute
      (bitonicSortByBits bitOrder keyFits depth ascending input) input := by
  unfold bitonicSortByBits
  have virtualRecordsPermute :=
    bitonicSortBits_recordsPermute keyFits depth ascending
      (reindexRecordBits bitOrder input)
  have physicalRecordsPermute :=
    virtualRecordsPermute.reindexRecordBits bitOrder.symm
  simpa using physicalRecordsPermute

theorem bitonicSortByCircuit_keysSorted
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatKeysSortedBy bitOrder keyFits ascending
      ((bitonicSortByCircuit bitOrder keyFits depth ascending).eval
        DeMorgan.interpretation input) := by
  rw [bitonicSortByCircuit_eval]
  exact bitonicSortByBits_keysSorted bitOrder keyFits depth ascending input

theorem bitonicSortByCircuit_recordsPermute
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatRecordsPermute
      ((bitonicSortByCircuit bitOrder keyFits depth ascending).eval
        DeMorgan.interpretation input) input := by
  rw [bitonicSortByCircuit_eval]
  exact bitonicSortByBits_recordsPermute bitOrder keyFits depth ascending input

@[simp] theorem bitonicSortByCircuit_cost
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool) :
    (bitonicSortByCircuit bitOrder keyFits depth ascending).cost
        DeMorgan.standardCost =
      (bitonicSortCircuit keyFits depth ascending).cost
        DeMorgan.standardCost := by
  simp [bitonicSortByCircuit]

theorem bitonicSortByCircuit_cost_le
    (bitOrder : Equiv.Perm (Fin recordWidth))
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool) :
    (bitonicSortByCircuit bitOrder keyFits depth ascending).cost
        DeMorgan.standardCost <=
      depth * depth * networkRecords depth *
        ((2 * recordWidth) *
          (2 * (keyWidth * (6 * keyWidth + 4)) + 4)) := by
  rw [bitonicSortByCircuit_cost]
  exact bitonicSortCircuit_cost_le keyFits depth ascending

end Sorting
end MassProduction
end Algebraic
