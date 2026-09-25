/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BroadcastRecords

/-!
# Canonical ordering after shared broadcast

A unique destination header with known rank determines a literal output
position after the second sort. This formulation separates ordering from the
matching method, so it also applies when destination matching keys repeat.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting RoutingMetadata CanonicalMetadataRouting

/-- Canonical sorting produces increasing physical destination headers. -/
theorem canonicalHeadersIncreasing
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool) :
    Semantics.SequenceIncreasing
      (fun record => recordHeader (flatRecords
        (canonicalSortBits depth keyWidth metadataWidth valueWidth input) record)) := by
  have sorted := canonicalSortBits_keysSorted input
  intro left right before
  have ordered := sorted left right before
  dsimp only at ordered
  rw [metadataOrderVirtualKey, metadataOrderVirtualKey] at ordered
  simpa only [recordHeader_flatRecords] using ordered

/-- Canonical sorting permutes exactly the complemented initial headers. -/
theorem canonicalHeadersPermute
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool) :
    Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords
        (canonicalSortBits depth keyWidth metadataWidth valueWidth input) record))
      (fun record => complementedRecordHeader (flatRecords input record)) := by
  have mapped := Semantics.SequencePermutes.map recordHeader
    (canonicalSortBits_recordsPermute input)
  simpa only [Function.comp_def, recordHeader_complementRoutingTagsBits] using mapped

/-- A unique header with known rank sends its associated value to a fixed
output wire. No restriction is imposed on its earlier matching key. -/
theorem canonicalSort_fixedValue
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (header : Lex (Fin (metadataWidth + 1) → Bool))
    (target : Fin (networkRecords depth)) (value : Fin valueWidth → Bool)
    (unique : Semantics.UniqueIndexWhere
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun candidate => candidate = header))
    (rank : (Semantics.matchingIndices
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun candidate => candidate < header)).card = target.val)
    (valueCorrect : ∀ record,
      complementedRecordHeader (flatRecords input record) = header →
        recordValue input record = value) :
    recordValue (canonicalSortBits depth keyWidth metadataWidth valueWidth input) target =
      value := by
  let output := canonicalSortBits depth keyWidth metadataWidth valueWidth input
  have headersPermute := canonicalHeadersPermute input
  obtain ⟨outputIndex, outputMatches, outputOnly⟩ :=
    Semantics.UniqueIndexWhere.of_sequencePermutes headersPermute unique
  have outputRank : (Semantics.matchingIndices
      (fun record => recordHeader (flatRecords output record))
      (fun candidate => candidate < header)).card = outputIndex.val := by
    rw [← outputMatches]
    apply Semantics.matchingIndices_lt_card_eq_index
      (fun record => recordHeader (flatRecords output record))
      (canonicalHeadersIncreasing input) outputIndex
    intro other equalHeader
    exact outputOnly other (equalHeader.trans outputMatches)
  have sameIndex : outputIndex = target := by
    apply Fin.ext
    exact outputRank.symm.trans
      ((headersPermute.matchingIndices_card_eq (fun candidate => candidate < header)).trans rank)
  subst outputIndex
  obtain ⟨inputIndex, sameRecord⟩ :=
    (canonicalSortBits_recordsPermute input).rangeContained target
  have sameHeader := congrArg recordHeader sameRecord
  rw [recordHeader_complementRoutingTagsBits] at sameHeader
  have initialMatches : complementedRecordHeader (flatRecords input inputIndex) = header :=
    sameHeader.symm.trans outputMatches
  have sameValue := congrArg packedRecordValue sameRecord
  simp only [packedRecordValue_flatRecords, recordValue_complementRoutingTagsBits] at sameValue
  exact sameValue.trans (valueCorrect inputIndex initialMatches)

end Algebraic.MassProduction.Nonuniform.Broadcast
