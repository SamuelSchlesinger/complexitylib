/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.CanonicalBroadcast

/-!
# Two-sort batched routing with repeated matching keys

The first sort places a unique source before arbitrarily many destinations.
The shared scan broadcasts values while preserving destination identifiers.
The second sort returns results to fixed output positions. All operations
are explicit De Morgan circuits with an additive cost bound.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting RoutingMetadata CanonicalMetadataRouting

/-- Sorting by matching key and tag, followed by shared value broadcast. -/
def sortedCircuit (depth keyWidth metadataWidth valueWidth : Nat) :=
  (recordsCircuit depth keyWidth metadataWidth valueWidth).comp
    (bitonicSortCircuit
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth true)

/-- The bitonic sort followed by the value broadcast. -/
@[simp] theorem sortedCircuit_size
    (depth keyWidth metadataWidth valueWidth : Nat) :
    (sortedCircuit depth keyWidth metadataWidth valueWidth).size =
      bitonicSortGateCount
          (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth +
        (recordsCircuit depth keyWidth metadataWidth valueWidth).size := by
  simp [sortedCircuit]

/-- The complete two-sort batched router. -/
def routingCircuit (depth keyWidth metadataWidth valueWidth : Nat) :=
  (canonicalSortCircuit depth keyWidth metadataWidth valueWidth).comp
    (sortedCircuit depth keyWidth metadataWidth valueWidth)

/-- The exact gate count of `routingCircuit`. -/
@[simp] theorem routingCircuit_size
    (depth keyWidth metadataWidth valueWidth : Nat) :
    (routingCircuit depth keyWidth metadataWidth valueWidth).size =
      (sortedCircuit depth keyWidth metadataWidth valueWidth).size +
        (canonicalSortCircuit depth keyWidth metadataWidth valueWidth).size := by
  simp [routingCircuit]

@[simp] theorem recordsCircuit_complementedHeader
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (record : Fin (networkRecords depth)) :
    complementedRecordHeader (flatRecords
      ((recordsCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) record) =
      complementedRecordHeader (flatRecords input record) := by
  simp [complementedRecordHeader]

/-- Matching and broadcast preserve the complete multiset of destination
identifiers, including padding identifiers. -/
theorem sortedCircuit_headersPermute
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool) :
    Semantics.SequencePermutes
      (fun record => complementedRecordHeader (flatRecords
        ((sortedCircuit depth keyWidth metadataWidth valueWidth).eval
          DeMorgan.interpretation input) record))
      (fun record => complementedRecordHeader (flatRecords input record)) := by
  simp only [sortedCircuit, Circuit.eval_comp, bitonicSortCircuit_eval,
    recordsCircuit_complementedHeader]
  exact Semantics.SequencePermutes.map complementedRecordHeader
    (bitonicSortBits_recordsPermute
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth true input)

/-- Every destination header specifying the query key receives the value
of its unique source. Destination keys may repeat. -/
theorem sortedCircuit_valueCorrect
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (header : Lex (Fin (metadataWidth + 1) → Bool))
    (key : Fin keyWidth → Bool) (value : Fin valueWidth → Bool)
    (uniqueSource : Semantics.UniqueIndexWhere (flatRecords input)
      (Routing.recordHasKeyTag key false))
    (sourceCorrect : ∀ record, Routing.recordKey input record = key →
      Routing.recordTag input record = false → recordValue input record = value)
    (queryCorrect : ∀ record,
      complementedRecordHeader (flatRecords input record) = header →
      Routing.recordKey input record = key ∧ Routing.recordTag input record = true)
    (destination : Fin (networkRecords depth))
    (destinationHeader : complementedRecordHeader (flatRecords
      ((sortedCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) destination) = header) :
    recordValue
      ((sortedCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) destination = value := by
  let sorted := bitonicSortBits
    (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth true input
  have permuted : FlatRecordsPermute sorted input :=
    bitonicSortBits_recordsPermute
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth true input
  have sortedHeader : complementedRecordHeader (flatRecords sorted destination) = header := by
    simpa only [sortedCircuit, Circuit.eval_comp, bitonicSortCircuit_eval,
      recordsCircuit_complementedHeader] using destinationHeader
  obtain ⟨originalDestination, sameDestination⟩ := permuted.rangeContained destination
  have originalHeader :
      complementedRecordHeader (flatRecords input originalDestination) = header :=
    (congrArg complementedRecordHeader sameDestination).symm.trans sortedHeader
  have originalFields := queryCorrect originalDestination originalHeader
  have destinationFields : Routing.recordKey sorted destination = key ∧
      Routing.recordTag sorted destination = true := by
    have keys := congrArg Routing.packedRecordKey sameDestination
    have tags := congrArg Routing.packedRecordTag sameDestination
    exact ⟨keys.trans originalFields.1, tags.trans originalFields.2⟩
  obtain ⟨source, sourceMatches, sourceOnly⟩ := permuted.uniqueIndexWhere uniqueSource
  have sourceFields :=
    (Routing.recordHasKeyTag_flatRecords_iff sorted source key false).mp sourceMatches
  have sourceUnique : ∀ index, Routing.recordKey sorted index = Routing.recordKey sorted source →
      Routing.recordTag sorted index = false → index = source := by
    intro index sameKey sourceTag
    apply sourceOnly index
    exact (Routing.recordHasKeyTag_flatRecords_iff sorted index key false).mpr
      ⟨sameKey.trans sourceFields.1, sourceTag⟩
  obtain ⟨originalSource, sameSource⟩ := permuted.rangeContained source
  have originalSourceFields : Routing.recordKey input originalSource = key ∧
      Routing.recordTag input originalSource = false := by
    have keys := congrArg Routing.packedRecordKey sameSource
    have tags := congrArg Routing.packedRecordTag sameSource
    exact ⟨keys.symm.trans sourceFields.1, tags.symm.trans sourceFields.2⟩
  have sourceValue : recordValue sorted source = value :=
    (congrArg packedRecordValue sameSource).trans
      (sourceCorrect originalSource originalSourceFields.1 originalSourceFields.2)
  have routed := recordsCircuit_routesSorted sorted
    (bitonicSortBits_keysSorted
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth true input)
    source destination (sourceFields.1.trans destinationFields.1.symm)
    sourceFields.2 destinationFields.2 sourceUnique
  simpa only [sortedCircuit, Circuit.eval_comp, bitonicSortCircuit_eval]
    using routed.trans sourceValue

/-- The concrete two-sort circuit returns each lookup result to the fixed
output position determined by its unique destination identifier. -/
theorem routingCircuit_fixedValue
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (header : Lex (Fin (metadataWidth + 1) → Bool))
    (target : Fin (networkRecords depth))
    (key : Fin keyWidth → Bool) (value : Fin valueWidth → Bool)
    (uniqueHeader : Semantics.UniqueIndexWhere
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun candidate => candidate = header))
    (rank : (Semantics.matchingIndices
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun candidate => candidate < header)).card = target.val)
    (uniqueSource : Semantics.UniqueIndexWhere (flatRecords input)
      (Routing.recordHasKeyTag key false))
    (sourceCorrect : ∀ record, Routing.recordKey input record = key →
      Routing.recordTag input record = false → recordValue input record = value)
    (queryCorrect : ∀ record,
      complementedRecordHeader (flatRecords input record) = header →
      Routing.recordKey input record = key ∧ Routing.recordTag input record = true) :
    recordValue
      ((routingCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) target = value := by
  rw [routingCircuit, Circuit.eval_comp, canonicalSortCircuit_eval]
  have permuted := sortedCircuit_headersPermute input
  apply canonicalSort_fixedValue _ header target value
  · exact Semantics.UniqueIndexWhere.of_sequencePermutes permuted uniqueHeader
  · exact (permuted.matchingIndices_card_eq (fun candidate => candidate < header)).trans rank
  · exact sortedCircuit_valueCorrect input header key value uniqueSource
      sourceCorrect queryCorrect

/-- The two sorts and shared scan have linear dependence on the record
count, with polynomial factors in depth and record-field widths. -/
theorem routingCircuit_cost_le :
    (routingCircuit depth keyWidth metadataWidth valueWidth).cost DeMorgan.standardCost ≤
      (depth * depth * networkRecords depth *
        ((2 * recordWidth keyWidth metadataWidth valueWidth) *
          (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkRecords depth * (valueWidth * (6 * keyWidth + 4))) +
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth) +
        depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth metadataWidth valueWidth) *
            (2 * ((metadataWidth + 1) * (6 * (metadataWidth + 1) + 4)) + 4))) := by
  rw [routingCircuit, Circuit.cost_comp, sortedCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (Nat.add_le_add
      (bitonicSortCircuit_cost_le
        (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth true)
      recordsCircuit_cost_le)
    canonicalSortCircuit_cost_le

end Algebraic.MassProduction.Nonuniform.Broadcast
