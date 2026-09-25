/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Routing
public import Mathlib.Order.Cover

/-!
# Correctness of sorted predecessor routing

The local routing scan is useful only after proving that its intended source
really is the destination's immediate predecessor.  This module isolates that
order-theoretic argument.  A strictly covered pair of unique keys must occupy
adjacent positions in an increasing finite sequence; applying that fact to the
verified Batcher output makes the guarded predecessor copy exact.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Routing

open Sorting
open Sorting.Semantics

/-! ## Transporting unique records through a sorting permutation -/

/-- Routing-namespace compatibility alias for the generic finite-sequence
uniqueness predicate. -/
abbrev UniqueIndexWhere
    (sequence : Fin n -> α)
    (predicate : α -> Prop) : Prop :=
  Sorting.Semantics.UniqueIndexWhere sequence predicate

/-- Routing-namespace compatibility alias for generic matching positions. -/
noncomputable abbrev matchingIndices
    (sequence : Fin n -> α)
    (predicate : α -> Prop) : Finset (Fin n) :=
  Sorting.Semantics.matchingIndices sequence predicate

/-- Routing-namespace compatibility alias for generic predicate reflection. -/
noncomputable abbrev predicateBit
    (predicate : α -> Prop) (value : α) : Bool :=
  Sorting.Semantics.predicateBit predicate value

/-- Routing-namespace compatibility theorem for unique matching positions. -/
theorem uniqueIndexWhere_iff_filter_card_eq_one
    (sequence : Fin n -> α)
    (predicate : α -> Prop) :
    UniqueIndexWhere sequence predicate ↔
      (matchingIndices sequence predicate).card = 1 :=
  Sorting.Semantics.UniqueIndexWhere.iff_matchingIndices_card_eq_one
    sequence predicate

/-- Routing-namespace compatibility theorem for predicate counting. -/
theorem countP_ofFn_eq_filter_card
    (sequence : Fin n -> α)
    (predicate : α -> Prop) :
    (List.ofFn sequence).countP
      (predicateBit predicate) =
      (matchingIndices sequence predicate).card :=
  Sorting.Semantics.countP_predicateBit_eq_matchingIndices_card
    sequence predicate

/-- Routing-namespace compatibility theorem for transporting a unique match
through a finite-sequence permutation. -/
theorem UniqueIndexWhere.of_sequencePermutes
    {output input : Fin n -> α}
    {predicate : α -> Prop}
    (permuted : SequencePermutes output input)
    (uniqueInput : UniqueIndexWhere input predicate) :
    UniqueIndexWhere output predicate := by
  simpa [UniqueIndexWhere, Sorting.Semantics.UniqueIndexWhere] using
    (Sorting.Semantics.UniqueIndexWhere.of_sequencePermutes
      permuted uniqueInput)

/-- Routing-namespace compatibility theorem for transporting a unique record
predicate through packed sorting. -/
theorem UniqueIndexWhere.of_flatRecordsPermute
    {output input : Fin (networkBits depth packedWidth) -> Bool}
    {predicate : (Fin packedWidth -> Bool) -> Prop}
    (permuted : FlatRecordsPermute output input)
    (uniqueInput : UniqueIndexWhere (flatRecords input) predicate) :
    UniqueIndexWhere (flatRecords output) predicate := by
  simpa [UniqueIndexWhere, Sorting.Semantics.UniqueIndexWhere] using
    (Sorting.FlatRecordsPermute.uniqueIndexWhere permuted uniqueInput)

/-- Routing-namespace compatibility theorem for the generic sequence result. -/
theorem SequencePermutes.rangeContained
    {output input : Fin n -> α}
    (permuted : SequencePermutes output input) :
    SequenceRangeContained output input :=
  Sorting.Semantics.SequencePermutes.rangeContained permuted

theorem FlatRecordsPermute.rangeContained
    {output input : Fin (networkBits depth packedWidth) -> Bool}
    (permuted : FlatRecordsPermute output input) :
    SequenceRangeContained (flatRecords output) (flatRecords input) :=
  Sorting.FlatRecordsPermute.rangeContained permuted

/-- In an increasing finite sequence, two uniquely occurring keys related by
`CovBy` occupy adjacent indices. -/
theorem adjacent_indices_of_increasing_covBy
    [LinearOrder κ]
    (sequence : Fin n -> κ)
    (increasing : SequenceIncreasing sequence)
    (source destination : Fin n)
    (covered : sequence source ⋖ sequence destination)
    (sourceUnique : ∀ index, sequence index = sequence source ->
      index = source)
    (destinationUnique : ∀ index,
      sequence index = sequence destination -> index = destination) :
    destination.val = source.val + 1 := by
  have sourceLtDestination : source < destination := by
    rcases lt_trichotomy source destination with
      sourceBefore | sameIndex | destinationBefore
    · exact sourceBefore
    · subst destination
      exact False.elim (lt_irrefl _ covered.lt)
    · have wrongOrder := increasing destination source destinationBefore
      exact False.elim ((not_le_of_gt covered.lt) wrongOrder)
  by_contra notAdjacent
  have gap : source.val + 1 < destination.val := by
    omega
  let middle : Fin n :=
    ⟨source.val + 1, lt_trans gap destination.isLt⟩
  have sourceBeforeMiddle : source < middle := by
    change source.val < source.val + 1
    omega
  have middleBeforeDestination : middle < destination := by
    exact gap
  have sourceLeMiddle := increasing source middle sourceBeforeMiddle
  have middleLeDestination :=
    increasing middle destination middleBeforeDestination
  rcases covered.eq_or_eq sourceLeMiddle middleLeDestination with
    middleIsSource | middleIsDestination
  · have indexEquality := sourceUnique middle middleIsSource
    have valueEquality := congrArg Fin.val indexEquality
    change source.val + 1 = source.val at valueEquality
    omega
  · have indexEquality := destinationUnique middle middleIsDestination
    have valueEquality := congrArg Fin.val indexEquality
    change source.val + 1 = destination.val at valueEquality
    omega

/-- Append the source/destination tag after all routing-key bits. -/
def keyWithTag
    (key : Fin keyWidth -> Bool)
    (tag : Bool) : Fin (keyWidth + 1) -> Bool :=
  Fin.snoc key tag

/-- There is no lexicographic Boolean key strictly between a fixed key tagged
as a source and the same key tagged as a destination. -/
theorem keyWithTag_false_covBy_true
    (key : Fin keyWidth -> Bool) :
    toLex (keyWithTag key false) ⋖
      toLex (keyWithTag key true) := by
  constructor
  · refine ⟨Fin.last keyWidth, ?_, ?_⟩
    · intro index indexBeforeLast
      obtain ⟨prefixIndex, rfl⟩ :=
        Fin.eq_castSucc_of_ne_last (ne_of_lt indexBeforeLast)
      simp [keyWithTag]
    · simp [keyWithTag]
  · intro middle sourceBeforeMiddle middleBeforeDestination
    change Pi.Lex (fun left right => left < right)
      (fun left right : Bool => left < right)
      (keyWithTag key false) (ofLex middle) at sourceBeforeMiddle
    change Pi.Lex (fun left right => left < right)
      (fun left right : Bool => left < right)
      (ofLex middle) (keyWithTag key true) at middleBeforeDestination
    obtain ⟨sourceWitness, sourceEqualBefore, sourceLessAt⟩ :=
      sourceBeforeMiddle
    obtain ⟨destinationWitness, destinationEqualBefore,
      destinationLessAt⟩ := middleBeforeDestination
    rcases lt_trichotomy sourceWitness destinationWitness with
      sourceWitnessBefore | witnessesEqual | destinationWitnessBefore
    · have endpointLess :
          keyWithTag key false sourceWitness <
            keyWithTag key true sourceWitness := by
        rw [← destinationEqualBefore sourceWitness sourceWitnessBefore]
        exact sourceLessAt
      have sourceWitnessLast : sourceWitness = Fin.last keyWidth := by
        by_contra notLast
        obtain ⟨prefixIndex, rfl⟩ :=
          Fin.eq_castSucc_of_ne_last notLast
        simp [keyWithTag] at endpointLess
      subst sourceWitness
      exact (not_lt_of_ge (Fin.le_last destinationWitness))
        sourceWitnessBefore
    · subst destinationWitness
      by_cases witnessLast : sourceWitness = Fin.last keyWidth
      · subst sourceWitness
        cases middleValue : ofLex middle (Fin.last keyWidth) with
        | false =>
            simp [keyWithTag, middleValue] at sourceLessAt
        | true =>
            simp [keyWithTag, middleValue] at destinationLessAt
      · have endpointsEqual :
            keyWithTag key false sourceWitness =
              keyWithTag key true sourceWitness := by
          obtain ⟨prefixIndex, rfl⟩ :=
            Fin.eq_castSucc_of_ne_last witnessLast
          simp [keyWithTag]
        have impossible := sourceLessAt.trans destinationLessAt
        rw [endpointsEqual] at impossible
        exact (lt_irrefl _ impossible)
    · have endpointLess :
          keyWithTag key false destinationWitness <
            keyWithTag key true destinationWitness := by
        rw [sourceEqualBefore destinationWitness destinationWitnessBefore]
        exact destinationLessAt
      have destinationWitnessLast :
          destinationWitness = Fin.last keyWidth := by
        by_contra notLast
        obtain ⟨prefixIndex, rfl⟩ :=
          Fin.eq_castSucc_of_ne_last notLast
        simp [keyWithTag] at endpointLess
      subst destinationWitness
      exact (not_lt_of_ge (Fin.le_last sourceWitness))
        destinationWitnessBefore

/-- The key used by a scatter/gather matching pass: physical key bits followed
by the source/destination tag. -/
def recordKeyAndTag
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    Lex (Fin (keyWidth + 1) -> Bool) :=
  flatRecordKey (keyAndTagFitsRecord keyWidth payloadWidth)
    (flatRecords input record)

/-- The prefix consumed by the sorter is exactly the routing key with its tag
appended in the final key position. -/
theorem recordKeyAndTag_eq_keyWithTag
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordKeyAndTag input record =
      toLex (keyWithTag (recordKey input record) (recordTag input record)) := by
  unfold recordKeyAndTag flatRecordKey
  rw [toLex_inj]
  funext bit
  refine Fin.lastCases ?_ (fun prefixBit => ?_) bit
  · simp only [keyWithTag, Fin.snoc_last]
    unfold flatRecords networkRecord recordTag
    apply congrArg input
    apply Fin.ext
    rfl
  · simp only [keyWithTag, Fin.snoc_castSucc]
    unfold flatRecords networkRecord recordKey
    apply congrArg input
    apply Fin.ext
    rfl

/-- Equality of the sorter's combined key is exactly equality of the physical
key and tag fields. -/
theorem recordKeyAndTag_eq_iff
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (left right : Fin (networkRecords depth)) :
    recordKeyAndTag input left = recordKeyAndTag input right ↔
      recordKey input left = recordKey input right ∧
        recordTag input left = recordTag input right := by
  rw [recordKeyAndTag_eq_keyWithTag,
    recordKeyAndTag_eq_keyWithTag, toLex_inj]
  exact Fin.snoc_inj

/-- Standalone-record predicate used to identify one source or destination
record before and after complete-record sorting. -/
def recordHasKeyTag
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (record : Fin (recordWidth keyWidth payloadWidth) -> Bool) : Prop :=
  packedRecordKey record = key ∧ packedRecordTag record = tag

theorem recordHasKeyTag_flatRecords_iff
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth))
    (key : Fin keyWidth -> Bool)
    (tag : Bool) :
    recordHasKeyTag key tag (flatRecords input record) ↔
      recordKey input record = key ∧ recordTag input record = tag := by
  rfl

/-- Same routing keys tagged `false` and `true` form a covering pair in the
sorter's lexicographic key order. -/
theorem recordKeyAndTag_covBy_of_sameKey
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (source destination : Fin (networkRecords depth))
    (sameKey : recordKey input source = recordKey input destination)
    (sourceTag : recordTag input source = false)
    (destinationTag : recordTag input destination = true) :
    recordKeyAndTag input source ⋖ recordKeyAndTag input destination := by
  rw [recordKeyAndTag_eq_keyWithTag,
    recordKeyAndTag_eq_keyWithTag, sourceTag, destinationTag, sameKey]
  exact keyWithTag_false_covBy_true (recordKey input destination)

/-- A sorted array places a uniquely occurring covered source key immediately
before its uniquely occurring destination key. -/
theorem predecessor_eq_of_sorted_covBy
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (sorted : FlatKeysSorted
      (keyAndTagFitsRecord keyWidth payloadWidth) true input)
    (source destination : Fin (networkRecords depth))
    (covered : recordKeyAndTag input source ⋖
      recordKeyAndTag input destination)
    (sourceUnique : ∀ index,
      recordKeyAndTag input index = recordKeyAndTag input source ->
        index = source)
    (destinationUnique : ∀ index,
      recordKeyAndTag input index = recordKeyAndTag input destination ->
        index = destination) :
    ∃ positive : 0 < destination.val,
      predecessor destination positive = source := by
  have increasing :
      SequenceIncreasing (recordKeyAndTag input) := by
    change SequenceIncreasing (fun record =>
      flatRecordKey (keyAndTagFitsRecord keyWidth payloadWidth)
        (flatRecords input record))
    simpa only [FlatKeysSorted, SequenceSorted, ite_true] using sorted
  have adjacent := adjacent_indices_of_increasing_covBy
    (recordKeyAndTag input) increasing source destination covered
      sourceUnique destinationUnique
  have positive : 0 < destination.val := by omega
  refine ⟨positive, ?_⟩
  apply Fin.ext
  change destination.val - 1 = source.val
  omega

/-- Once the source/destination keys are known to be adjacent, the explicit
guarded scan copies the complete payload of the intended source record. -/
theorem predecessorCopyBits_recordPayload_of_sorted_covBy
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (sorted : FlatKeysSorted
      (keyAndTagFitsRecord keyWidth payloadWidth) true input)
    (source destination : Fin (networkRecords depth))
    (covered : recordKeyAndTag input source ⋖
      recordKeyAndTag input destination)
    (sourceUnique : ∀ index,
      recordKeyAndTag input index = recordKeyAndTag input source ->
        index = source)
    (destinationUnique : ∀ index,
      recordKeyAndTag input index = recordKeyAndTag input destination ->
        index = destination)
    (sameKey : recordKey input source = recordKey input destination)
    (sourceHasTag : recordTag input source = sourceTag)
    (destinationHasTag : recordTag input destination = destinationTag) :
    recordPayload
        (predecessorCopyBits depth keyWidth payloadWidth
          sourceTag destinationTag input) destination =
      recordPayload input source := by
  obtain ⟨positive, predecessorEquality⟩ :=
    predecessor_eq_of_sorted_covBy input sorted source destination covered
      sourceUnique destinationUnique
  have copied := predecessorCopyBits_recordPayload_of_match
    sourceTag destinationTag input destination positive
      (by simpa only [predecessorEquality] using sameKey)
      (by simpa only [predecessorEquality] using sourceHasTag)
      destinationHasTag
  simpa only [predecessorEquality] using copied

/-- Sorting by `(key, tag)` and scanning predecessors routes a unique source
payload to the unique same-key destination.  The source tag is `false` and the
destination tag is `true`, matching the order used by the manuscript. -/
theorem predecessorCopyBits_recordPayload_of_sorted_unique
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (sorted : FlatKeysSorted
      (keyAndTagFitsRecord keyWidth payloadWidth) true input)
    (source destination : Fin (networkRecords depth))
    (sourceUnique : ∀ index,
      recordKeyAndTag input index = recordKeyAndTag input source ->
        index = source)
    (destinationUnique : ∀ index,
      recordKeyAndTag input index = recordKeyAndTag input destination ->
        index = destination)
    (sameKey : recordKey input source = recordKey input destination)
    (sourceTag : recordTag input source = false)
    (destinationTag : recordTag input destination = true) :
    recordPayload
        (predecessorCopyBits depth keyWidth payloadWidth false true input)
        destination =
      recordPayload input source := by
  exact predecessorCopyBits_recordPayload_of_sorted_covBy false true input
    sorted source destination
      (recordKeyAndTag_covBy_of_sameKey input source destination sameKey
        sourceTag destinationTag)
      sourceUnique destinationUnique sameKey sourceTag destinationTag

/-- End-to-end correctness of the explicit sort-and-match circuit under the
unique source/destination record invariant. -/
theorem sortedPredecessorCopyCircuit_routes_unique
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (source destination : Fin (networkRecords depth))
    (sourceUnique : ∀ index,
      recordKeyAndTag
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          index =
        recordKeyAndTag
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          source -> index = source)
    (destinationUnique : ∀ index,
      recordKeyAndTag
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          index =
        recordKeyAndTag
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          destination -> index = destination)
    (sameKey :
      recordKey
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          source =
        recordKey
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          destination)
    (sourceTag :
      recordTag
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          source = false)
    (destinationTag :
      recordTag
          (bitonicSortBits
            (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
          destination = true) :
    recordPayload
        ((sortedPredecessorCopyCircuit depth keyWidth payloadWidth false true).eval
          DeMorgan.interpretation input) destination =
      recordPayload
        (bitonicSortBits
          (keyAndTagFitsRecord keyWidth payloadWidth) depth true input)
        source := by
  rw [sortedPredecessorCopyCircuit_eval]
  apply predecessorCopyBits_recordPayload_of_sorted_unique
  · exact bitonicSortBits_keysSorted
      (keyAndTagFitsRecord keyWidth payloadWidth) depth true input
  · exact sourceUnique
  · exact destinationUnique
  · exact sameKey
  · exact sourceTag
  · exact destinationTag

/-- Turn the router's position-level theorem into a packing-friendly API.
If the unsorted input contains exactly one source and one destination with a
given key, the explicit sort-and-copy circuit has a destination carrying the
original source payload. -/
theorem sortedPredecessorCopyCircuit_routes_unique_key
    (input : Fin (networkBits depth
      (recordWidth keyWidth payloadWidth)) -> Bool)
    (key : Fin keyWidth -> Bool)
    (uniqueSource : UniqueIndexWhere (flatRecords input)
      (recordHasKeyTag key false))
    (uniqueDestination : UniqueIndexWhere (flatRecords input)
      (recordHasKeyTag key true)) :
    let sorted := bitonicSortBits
      (keyAndTagFitsRecord keyWidth payloadWidth) depth true input
    ∃ sourceInput sourceSorted destinationSorted,
      recordHasKeyTag key false (flatRecords input sourceInput) ∧
      recordHasKeyTag key false (flatRecords sorted sourceSorted) ∧
      recordHasKeyTag key true (flatRecords sorted destinationSorted) ∧
      recordPayload
          ((sortedPredecessorCopyCircuit depth keyWidth payloadWidth
            false true).eval DeMorgan.interpretation input)
          destinationSorted =
        packedRecordPayload (flatRecords input sourceInput) := by
  classical
  let sorted := bitonicSortBits
    (keyAndTagFitsRecord keyWidth payloadWidth) depth true input
  have recordsPermute : FlatRecordsPermute sorted input :=
    bitonicSortBits_recordsPermute
      (keyAndTagFitsRecord keyWidth payloadWidth) depth true input
  have uniqueSourceSorted :=
    Sorting.FlatRecordsPermute.uniqueIndexWhere recordsPermute uniqueSource
  have uniqueDestinationSorted :=
    Sorting.FlatRecordsPermute.uniqueIndexWhere recordsPermute
      uniqueDestination
  obtain ⟨sourceInput, sourceInputMatches, sourceInputOnly⟩ := uniqueSource
  obtain ⟨sourceSorted, sourceSortedMatches, sourceSortedOnly⟩ :=
    uniqueSourceSorted
  obtain ⟨destinationSorted, destinationSortedMatches,
      destinationSortedOnly⟩ :=
    uniqueDestinationSorted
  have sourceFields :
      recordKey sorted sourceSorted = key ∧
        recordTag sorted sourceSorted = false :=
    (recordHasKeyTag_flatRecords_iff sorted sourceSorted key false).mp
      sourceSortedMatches
  have destinationFields :
      recordKey sorted destinationSorted = key ∧
        recordTag sorted destinationSorted = true :=
    (recordHasKeyTag_flatRecords_iff sorted destinationSorted key true).mp
      destinationSortedMatches
  have sourceKeyUnique : ∀ index,
      recordKeyAndTag sorted index =
          recordKeyAndTag sorted sourceSorted ->
        index = sourceSorted := by
    intro index equalKeyTag
    apply sourceSortedOnly index
    apply (recordHasKeyTag_flatRecords_iff sorted index key false).mpr
    have fields :=
      (recordKeyAndTag_eq_iff sorted index sourceSorted).mp equalKeyTag
    exact ⟨fields.1.trans sourceFields.1,
      fields.2.trans sourceFields.2⟩
  have destinationKeyUnique : ∀ index,
      recordKeyAndTag sorted index =
          recordKeyAndTag sorted destinationSorted ->
        index = destinationSorted := by
    intro index equalKeyTag
    apply destinationSortedOnly index
    apply (recordHasKeyTag_flatRecords_iff sorted index key true).mpr
    have fields :=
      (recordKeyAndTag_eq_iff sorted index destinationSorted).mp equalKeyTag
    exact ⟨fields.1.trans destinationFields.1,
      fields.2.trans destinationFields.2⟩
  have routed :
      recordPayload
          ((sortedPredecessorCopyCircuit depth keyWidth payloadWidth
            false true).eval DeMorgan.interpretation input)
          destinationSorted =
        recordPayload sorted sourceSorted := by
    apply sortedPredecessorCopyCircuit_routes_unique input
      sourceSorted destinationSorted sourceKeyUnique destinationKeyUnique
    · exact sourceFields.1.trans destinationFields.1.symm
    · exact sourceFields.2
    · exact destinationFields.2
  obtain ⟨correspondingInput, sourceRecordEquality⟩ :=
    FlatRecordsPermute.rangeContained recordsPermute sourceSorted
  have correspondingMatches :
      recordHasKeyTag key false
        (flatRecords input correspondingInput) := by
    rw [← sourceRecordEquality]
    exact sourceSortedMatches
  have correspondingEquality :=
    sourceInputOnly correspondingInput correspondingMatches
  subst correspondingInput
  have sourcePayloadEquality :
      recordPayload sorted sourceSorted =
        packedRecordPayload (flatRecords input sourceInput) := by
    change packedRecordPayload (flatRecords sorted sourceSorted) =
      packedRecordPayload (flatRecords input sourceInput)
    rw [sourceRecordEquality]
  exact ⟨sourceInput, sourceSorted, destinationSorted,
    sourceInputMatches, sourceSortedMatches, destinationSortedMatches,
    routed.trans sourcePayloadEquality⟩

end Routing
end MassProduction
end Algebraic
