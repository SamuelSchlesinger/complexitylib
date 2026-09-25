/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.CanonicalScatter

/-!
# Routing records with preserved ordering metadata

Gather records are matched by `(group, point)` but finally ordered by
`(request, line position)`.  These are different keys.  This module extends
the basic record layout to

`(matching key, tag, preserved metadata, copied value)`.

The predecessor pass updates only the value field of a matched destination;
its ordering metadata stays with the destination record.  This is the exact
layout needed for the manuscript's two gather sorts.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace RoutingMetadata

open scoped BigOperators
open Sorting

/-- Width of a routing record with an additional preserved metadata field. -/
abbrev recordWidth (keyWidth metadataWidth valueWidth : Nat) : Nat :=
  Routing.recordWidth keyWidth (metadataWidth + valueWidth)

/-- Physical index of one metadata bit. -/
def metadataBit
    (keyWidth metadataWidth valueWidth : Nat)
    (bit : Fin metadataWidth) :
    Fin (recordWidth keyWidth metadataWidth valueWidth) :=
  Routing.payloadBit keyWidth (metadataWidth + valueWidth)
    (Fin.castAdd valueWidth bit)

/-- Physical index of one copied-value bit. -/
def valueBit
    (keyWidth metadataWidth valueWidth : Nat)
    (bit : Fin valueWidth) :
    Fin (recordWidth keyWidth metadataWidth valueWidth) :=
  Routing.payloadBit keyWidth (metadataWidth + valueWidth)
    (Fin.natAdd metadataWidth bit)

/-- Metadata projection from one flat record array. -/
def recordMetadata
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) : Fin metadataWidth -> Bool :=
  fun bit => input (Routing.recordBitIndex depth keyWidth
    (metadataWidth + valueWidth) record
    (metadataBit keyWidth metadataWidth valueWidth bit))

/-- Copied-value projection from one flat record array. -/
def recordValue
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) : Fin valueWidth -> Bool :=
  fun bit => input (Routing.recordBitIndex depth keyWidth
    (metadataWidth + valueWidth) record
    (valueBit keyWidth metadataWidth valueWidth bit))

/-- Pack one metadata-aware routing record. -/
def packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (metadata : Fin metadataWidth -> Bool)
    (value : Fin valueWidth -> Bool) :
    Fin (recordWidth keyWidth metadataWidth valueWidth) -> Bool :=
  Routing.packRecord key tag (Fin.append metadata value)

@[simp] theorem packedRecordKey_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (metadata : Fin metadataWidth -> Bool)
    (value : Fin valueWidth -> Bool) :
    Routing.packedRecordKey (packRecord key tag metadata value) = key := by
  simp [packRecord]

@[simp] theorem packedRecordTag_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (metadata : Fin metadataWidth -> Bool)
    (value : Fin valueWidth -> Bool) :
    Routing.packedRecordTag (packRecord key tag metadata value) = tag := by
  simp [packRecord]

/-- Metadata projection from one standalone record. -/
def packedRecordMetadata
    (record : Fin (recordWidth keyWidth metadataWidth valueWidth) -> Bool) :
    Fin metadataWidth -> Bool :=
  fun bit => record (metadataBit keyWidth metadataWidth valueWidth bit)

/-- Value projection from one standalone record. -/
def packedRecordValue
    (record : Fin (recordWidth keyWidth metadataWidth valueWidth) -> Bool) :
    Fin valueWidth -> Bool :=
  fun bit => record (valueBit keyWidth metadataWidth valueWidth bit)

@[simp] theorem packedRecordMetadata_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (metadata : Fin metadataWidth -> Bool)
    (value : Fin valueWidth -> Bool) :
    packedRecordMetadata (packRecord key tag metadata value) = metadata := by
  funext bit
  change Routing.packedRecordPayload
      (Routing.packRecord key tag (Fin.append metadata value))
      (Fin.castAdd valueWidth bit) = metadata bit
  rw [Routing.packedRecordPayload_packRecord, Fin.append_left]

@[simp] theorem packedRecordValue_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (metadata : Fin metadataWidth -> Bool)
    (value : Fin valueWidth -> Bool) :
    packedRecordValue (packRecord key tag metadata value) = value := by
  funext bit
  change Routing.packedRecordPayload
      (Routing.packRecord key tag (Fin.append metadata value))
      (Fin.natAdd metadataWidth bit) = value bit
  rw [Routing.packedRecordPayload_packRecord, Fin.append_right]

@[simp] theorem packedRecordMetadata_flatRecords
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    packedRecordMetadata (flatRecords input record) =
      recordMetadata input record := by
  rfl

@[simp] theorem packedRecordValue_flatRecords
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    packedRecordValue (flatRecords input record) = recordValue input record := by
  rfl

/-! ## Guarded value-only predecessor copy -/

/-- One output formula.  Headers and metadata are preserved; only the final
value field is conditionally copied. -/
def predecessorCopyOutputExpression
    (depth keyWidth metadataWidth valueWidth : Nat)
    (sourceTag destinationTag : Bool)
    (output : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth))) :
    DeMorgan.Expression
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) :=
  let recordAndBit :=
    (finProdFinEquiv
      (m := networkRecords depth)
      (n := recordWidth keyWidth metadataWidth valueWidth)).symm output
  if value : keyWidth + 1 + metadataWidth <= recordAndBit.2.val then
    if positive : 0 < recordAndBit.1.val then
      let valueIndex : Fin valueWidth :=
        ⟨recordAndBit.2.val - (keyWidth + 1 + metadataWidth), by
          have bound := recordAndBit.2.isLt
          unfold recordWidth Routing.recordWidth at bound
          omega⟩
      Sorting.muxExpression
        (Routing.predecessorMatchExpression depth keyWidth
          (metadataWidth + valueWidth) sourceTag destinationTag
          recordAndBit.1 positive)
        (.input (Routing.recordBitIndex depth keyWidth
          (metadataWidth + valueWidth)
          (Routing.predecessor recordAndBit.1 positive)
          (valueBit keyWidth metadataWidth valueWidth valueIndex)))
        (.constant false)
    else .constant false
  else .input output

/-- Semantic value-only predecessor copy. -/
def predecessorCopyBits
    (depth keyWidth metadataWidth valueWidth : Nat)
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool :=
  fun output =>
    (predecessorCopyOutputExpression depth keyWidth metadataWidth valueWidth
      sourceTag destinationTag output).eval input

/-- Gate count of one output expression in the value-only predecessor-copy
pass. -/
@[reducible] def predecessorCopyOutputGateCount
    (depth keyWidth metadataWidth valueWidth : Nat)
    (sourceTag destinationTag : Bool)
    (output : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth))) : Nat :=
  (predecessorCopyOutputExpression depth keyWidth metadataWidth valueWidth
    sourceTag destinationTag output).gateCount

/-- Explicit complete value-only copy pass. -/
def predecessorCopyCircuit
    (depth keyWidth metadataWidth valueWidth : Nat)
    (sourceTag destinationTag : Bool) :
    Circuit DeMorgan.signature
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))
      (∑ output, predecessorCopyOutputGateCount depth keyWidth metadataWidth
        valueWidth sourceTag destinationTag output)
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) :=
  Circuit.parallelFin
    (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))
    (predecessorCopyOutputGateCount depth keyWidth metadataWidth valueWidth
      sourceTag destinationTag) fun output =>
      (predecessorCopyOutputExpression depth keyWidth metadataWidth valueWidth
        sourceTag destinationTag output).circuit

@[simp] theorem predecessorCopyCircuit_eval
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    (predecessorCopyCircuit depth keyWidth metadataWidth valueWidth
        sourceTag destinationTag).eval DeMorgan.interpretation input =
      predecessorCopyBits depth keyWidth metadataWidth valueWidth
        sourceTag destinationTag input := by
  funext output
  rw [predecessorCopyCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  rfl

@[simp] theorem predecessorCopyBits_recordKey
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    Routing.recordKey
        (predecessorCopyBits depth keyWidth metadataWidth valueWidth
          sourceTag destinationTag input) record =
      Routing.recordKey input record := by
  funext bit
  unfold Routing.recordKey predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [Routing.finProdFinEquiv_symm_recordBitIndex]
  have beforeValue :
      Not (keyWidth + 1 + metadataWidth <=
        (Routing.keyBit keyWidth (metadataWidth + valueWidth) bit).val) := by
    change Not (keyWidth + 1 + metadataWidth <= bit.val)
    omega
  rw [dite_eq_right beforeValue]
  rfl

@[simp] theorem predecessorCopyBits_recordTag
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    Routing.recordTag
        (predecessorCopyBits depth keyWidth metadataWidth valueWidth
          sourceTag destinationTag input) record =
      Routing.recordTag input record := by
  unfold Routing.recordTag predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [Routing.finProdFinEquiv_symm_recordBitIndex]
  have beforeValue :
      Not (keyWidth + 1 + metadataWidth <=
        (Routing.tagBit keyWidth (metadataWidth + valueWidth)).val) := by
    change Not (keyWidth + 1 + metadataWidth <= keyWidth)
    omega
  rw [dite_eq_right beforeValue]
  rfl

@[simp] theorem predecessorCopyBits_recordMetadata
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordMetadata
        (predecessorCopyBits depth keyWidth metadataWidth valueWidth
          sourceTag destinationTag input) record =
      recordMetadata input record := by
  funext bit
  unfold recordMetadata predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [Routing.finProdFinEquiv_symm_recordBitIndex]
  have beforeValue :
      Not (keyWidth + 1 + metadataWidth <=
        (metadataBit keyWidth metadataWidth valueWidth bit).val) := by
    change Not (keyWidth + 1 + metadataWidth <= keyWidth + 1 + bit.val)
    omega
  rw [dite_eq_right beforeValue]
  rfl

/-- A positive record copies the predecessor value exactly when the same
key/tag guard succeeds. -/
theorem predecessorCopyBits_recordValue_of_positive
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val) :
    recordValue
        (predecessorCopyBits depth keyWidth metadataWidth valueWidth
          sourceTag destinationTag input) current =
      if (Routing.predecessorMatchExpression depth keyWidth
          (metadataWidth + valueWidth) sourceTag destinationTag
          current positive).eval input then
        recordValue input (Routing.predecessor current positive)
      else fun _ => false := by
  funext bit
  unfold recordValue predecessorCopyBits
  unfold predecessorCopyOutputExpression
  simp only [Routing.finProdFinEquiv_symm_recordBitIndex]
  have isValue : keyWidth + 1 + metadataWidth <=
      (valueBit keyWidth metadataWidth valueWidth bit).val := by
    change keyWidth + 1 + metadataWidth <=
      keyWidth + 1 + (metadataWidth + bit.val)
    omega
  rw [dite_eq_left isValue, dite_eq_left positive]
  have valueIndexEquality :
      (⟨(valueBit keyWidth metadataWidth valueWidth bit).val -
          (keyWidth + 1 + metadataWidth), by
        have bound := (valueBit keyWidth metadataWidth valueWidth bit).isLt
        unfold recordWidth Routing.recordWidth at bound
        omega⟩ : Fin valueWidth) = bit := by
    apply Fin.ext
    change (keyWidth + 1 + (metadataWidth + bit.val)) -
      (keyWidth + 1 + metadataWidth) = bit.val
    omega
  rw [valueIndexEquality, Sorting.muxExpression_eval]
  by_cases guardTrue :
      (Routing.predecessorMatchExpression depth keyWidth
        (metadataWidth + valueWidth) sourceTag destinationTag
        current positive).eval input = true <;>
    simp [guardTrue, DeMorgan.Expression.eval]

/-- A correctly tagged same-key predecessor is copied exactly. -/
theorem predecessorCopyBits_recordValue_of_match
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (current : Fin (networkRecords depth))
    (positive : 0 < current.val)
    (sameKey : Routing.recordKey input
        (Routing.predecessor current positive) =
      Routing.recordKey input current)
    (previousTag : Routing.recordTag input
        (Routing.predecessor current positive) = sourceTag)
    (currentTag : Routing.recordTag input current = destinationTag) :
    recordValue
        (predecessorCopyBits depth keyWidth metadataWidth valueWidth
          sourceTag destinationTag input) current =
      recordValue input (Routing.predecessor current positive) := by
  rw [predecessorCopyBits_recordValue_of_positive
    sourceTag destinationTag input current positive]
  have matched :
      (Routing.predecessorMatchExpression depth keyWidth
        (metadataWidth + valueWidth) sourceTag destinationTag
        current positive).eval input = true :=
    (Routing.predecessorMatchExpression_eval_eq_true_iff
      sourceTag destinationTag input current positive).mpr
        ⟨sameKey, previousTag, currentTag⟩
  rw [matched]
  rfl

/-- In a sorted array, a uniquely occurring same-key source/destination pair
routes its value while leaving destination metadata untouched. -/
theorem predecessorCopyBits_recordValue_of_sorted_unique
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (sorted : FlatKeysSorted
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
      true input)
    (source destination : Fin (networkRecords depth))
    (sourceUnique : forall index,
      Routing.recordKeyAndTag input index =
        Routing.recordKeyAndTag input source -> index = source)
    (destinationUnique : forall index,
      Routing.recordKeyAndTag input index =
        Routing.recordKeyAndTag input destination -> index = destination)
    (sameKey : Routing.recordKey input source =
      Routing.recordKey input destination)
    (sourceTag : Routing.recordTag input source = false)
    (destinationTag : Routing.recordTag input destination = true) :
    recordValue
        (predecessorCopyBits depth keyWidth metadataWidth valueWidth
          false true input) destination =
      recordValue input source := by
  have covered := Routing.recordKeyAndTag_covBy_of_sameKey input
    source destination sameKey sourceTag destinationTag
  obtain ⟨positive, predecessorEquality⟩ :=
    Routing.predecessor_eq_of_sorted_covBy input sorted source destination
      covered sourceUnique destinationUnique
  have copied := predecessorCopyBits_recordValue_of_match false true input
    destination positive
    (by simpa only [predecessorEquality] using sameKey)
    (by simpa only [predecessorEquality] using sourceTag)
    destinationTag
  simpa only [predecessorEquality] using copied

theorem predecessorCopyOutputExpression_standardCost_le
    (sourceTag destinationTag : Bool)
    (output : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth))) :
    (predecessorCopyOutputExpression depth keyWidth metadataWidth valueWidth
      sourceTag destinationTag output).standardCost <=
        12 * keyWidth + 12 := by
  unfold predecessorCopyOutputExpression
  dsimp only
  split_ifs with value positive
  · rw [Sorting.muxExpression_standardCost]
    simp only [DeMorgan.Expression.standardCost, Nat.add_zero]
    have guardBound := Routing.predecessorMatchExpression_standardCost_le
      (depth := depth) (keyWidth := keyWidth)
      (payloadWidth := metadataWidth + valueWidth)
      sourceTag destinationTag _ positive
    omega
  · simp [DeMorgan.Expression.standardCost]
  · simp [DeMorgan.Expression.standardCost]

theorem predecessorCopyCircuit_cost_le
    (sourceTag destinationTag : Bool) :
    (predecessorCopyCircuit depth keyWidth metadataWidth valueWidth
      sourceTag destinationTag).cost DeMorgan.standardCost <=
        networkBits depth (recordWidth keyWidth metadataWidth valueWidth) *
          (12 * keyWidth + 12) := by
  rw [predecessorCopyCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    (∑ output,
      (predecessorCopyOutputExpression depth keyWidth metadataWidth valueWidth
        sourceTag destinationTag output).standardCost) <=
        ∑ _output : Fin (networkBits depth
          (recordWidth keyWidth metadataWidth valueWidth)),
          (12 * keyWidth + 12) := by
      exact Finset.sum_le_sum fun output _ =>
        predecessorCopyOutputExpression_standardCost_le
          sourceTag destinationTag output
    _ = networkBits depth (recordWidth keyWidth metadataWidth valueWidth) *
        (12 * keyWidth + 12) := by simp

/-! ## Sort and value-copy composition -/

/-- Total gate count of sorting followed by value-only predecessor copying. -/
@[reducible] def sortedPredecessorCopyGateCount
    (depth keyWidth metadataWidth valueWidth : Nat)
    (sourceTag destinationTag : Bool) : Nat :=
  bitonicSortGateCount
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth +
    ∑ output, predecessorCopyOutputGateCount depth keyWidth metadataWidth
      valueWidth sourceTag destinationTag output

/-- Sort by `(matching key, tag)` and copy only the value field. -/
def sortedPredecessorCopyCircuit
    (depth keyWidth metadataWidth valueWidth : Nat)
    (sourceTag destinationTag : Bool) :
    Circuit DeMorgan.signature
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth))
      (sortedPredecessorCopyGateCount depth keyWidth metadataWidth valueWidth
        sourceTag destinationTag)
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) :=
  (predecessorCopyCircuit depth keyWidth metadataWidth valueWidth
    sourceTag destinationTag).comp
      (bitonicSortCircuit
        (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
        depth true)

@[simp] theorem sortedPredecessorCopyCircuit_eval
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    (sortedPredecessorCopyCircuit depth keyWidth metadataWidth valueWidth
      sourceTag destinationTag).eval DeMorgan.interpretation input =
        predecessorCopyBits depth keyWidth metadataWidth valueWidth
          sourceTag destinationTag
          (bitonicSortBits
            (Routing.keyAndTagFitsRecord keyWidth
              (metadataWidth + valueWidth)) depth true input) := by
  rw [sortedPredecessorCopyCircuit, Circuit.eval_comp,
    predecessorCopyCircuit_eval, bitonicSortCircuit_eval]

theorem sortedPredecessorCopyCircuit_cost_le
    (sourceTag destinationTag : Bool) :
    (sortedPredecessorCopyCircuit depth keyWidth metadataWidth valueWidth
      sourceTag destinationTag).cost DeMorgan.standardCost <=
      depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth metadataWidth valueWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkBits depth (recordWidth keyWidth metadataWidth valueWidth) *
          (12 * keyWidth + 12) := by
  rw [sortedPredecessorCopyCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (bitonicSortCircuit_cost_le
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
      depth true)
    (predecessorCopyCircuit_cost_le sourceTag destinationTag)

/-! ## Packing-friendly correctness API -/

/-- Sorting and value-only predecessor copying routes a unique source value
to the unique same-key destination. -/
theorem sortedPredecessorCopyCircuit_routes_unique_key
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (key : Fin keyWidth -> Bool)
    (uniqueSource : Sorting.Semantics.UniqueIndexWhere (flatRecords input)
      (Routing.recordHasKeyTag key false))
    (uniqueDestination : Sorting.Semantics.UniqueIndexWhere (flatRecords input)
      (Routing.recordHasKeyTag key true)) :
    let sorted := bitonicSortBits
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
      depth true input
    exists sourceInput sourceSorted destinationSorted,
      Routing.recordHasKeyTag key false (flatRecords input sourceInput) /\
      Routing.recordHasKeyTag key false (flatRecords sorted sourceSorted) /\
      Routing.recordHasKeyTag key true
        (flatRecords sorted destinationSorted) /\
      recordValue
          ((sortedPredecessorCopyCircuit depth keyWidth metadataWidth
            valueWidth false true).eval DeMorgan.interpretation input)
          destinationSorted =
        packedRecordValue (flatRecords input sourceInput) := by
  classical
  let sorted := bitonicSortBits
    (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
    depth true input
  have recordsPermute : FlatRecordsPermute sorted input :=
    bitonicSortBits_recordsPermute
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
      depth true input
  have uniqueSourceSorted :=
    Sorting.FlatRecordsPermute.uniqueIndexWhere recordsPermute uniqueSource
  have uniqueDestinationSorted :=
    Sorting.FlatRecordsPermute.uniqueIndexWhere recordsPermute
      uniqueDestination
  obtain ⟨sourceInput, sourceInputMatches, sourceInputOnly⟩ := uniqueSource
  obtain ⟨sourceSorted, sourceSortedMatches, sourceSortedOnly⟩ :=
    uniqueSourceSorted
  obtain ⟨destinationSorted, destinationSortedMatches,
      destinationSortedOnly⟩ := uniqueDestinationSorted
  have sourceFields :
      Routing.recordKey sorted sourceSorted = key /\
        Routing.recordTag sorted sourceSorted = false :=
    (Routing.recordHasKeyTag_flatRecords_iff sorted sourceSorted key false).mp
      sourceSortedMatches
  have destinationFields :
      Routing.recordKey sorted destinationSorted = key /\
        Routing.recordTag sorted destinationSorted = true :=
    (Routing.recordHasKeyTag_flatRecords_iff sorted destinationSorted key
      true).mp destinationSortedMatches
  have sourceKeyUnique : forall index,
      Routing.recordKeyAndTag sorted index =
          Routing.recordKeyAndTag sorted sourceSorted ->
        index = sourceSorted := by
    intro index equalKeyTag
    apply sourceSortedOnly index
    apply (Routing.recordHasKeyTag_flatRecords_iff sorted index key false).mpr
    have fields :=
      (Routing.recordKeyAndTag_eq_iff sorted index sourceSorted).mp equalKeyTag
    exact ⟨fields.1.trans sourceFields.1,
      fields.2.trans sourceFields.2⟩
  have destinationKeyUnique : forall index,
      Routing.recordKeyAndTag sorted index =
          Routing.recordKeyAndTag sorted destinationSorted ->
        index = destinationSorted := by
    intro index equalKeyTag
    apply destinationSortedOnly index
    apply (Routing.recordHasKeyTag_flatRecords_iff sorted index key true).mpr
    have fields :=
      (Routing.recordKeyAndTag_eq_iff sorted index destinationSorted).mp
        equalKeyTag
    exact ⟨fields.1.trans destinationFields.1,
      fields.2.trans destinationFields.2⟩
  have routed :
      recordValue
          ((sortedPredecessorCopyCircuit depth keyWidth metadataWidth
            valueWidth false true).eval DeMorgan.interpretation input)
          destinationSorted =
        recordValue sorted sourceSorted := by
    rw [sortedPredecessorCopyCircuit_eval]
    apply predecessorCopyBits_recordValue_of_sorted_unique sorted
      (bitonicSortBits_keysSorted
        (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
        depth true input)
      sourceSorted destinationSorted sourceKeyUnique destinationKeyUnique
    · exact sourceFields.1.trans destinationFields.1.symm
    · exact sourceFields.2
    · exact destinationFields.2
  obtain ⟨correspondingInput, sourceRecordEquality⟩ :=
    Sorting.FlatRecordsPermute.rangeContained recordsPermute sourceSorted
  have correspondingMatches : Routing.recordHasKeyTag key false
      (flatRecords input correspondingInput) := by
    rw [← sourceRecordEquality]
    exact sourceSortedMatches
  have correspondingEquality :=
    sourceInputOnly correspondingInput correspondingMatches
  subst correspondingInput
  have sourceValueEquality :
      recordValue sorted sourceSorted =
        packedRecordValue (flatRecords input sourceInput) := by
    change packedRecordValue (flatRecords sorted sourceSorted) =
      packedRecordValue (flatRecords input sourceInput)
    rw [sourceRecordEquality]
  exact ⟨sourceInput, sourceSorted, destinationSorted,
    sourceInputMatches, sourceSortedMatches, destinationSortedMatches,
    routed.trans sourceValueEquality⟩

end RoutingMetadata
end MassProduction
end Algebraic
