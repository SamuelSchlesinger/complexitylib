/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchRouting

/-!
# Batched OR lookup without source uniqueness

The same shared broadcast router can aggregate Boolean source flags. A
destination receives true exactly when some same-key source is true. This
allows repeated occupied-point descriptions and returns false for points
that are absent from the occupied set.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting RoutingMetadata CanonicalMetadataRouting

/-- Broadcast OR correctness before the final ordering pass. -/
theorem sortedCircuit_valueOr
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (header : Lex (Fin (metadataWidth + 1) → Bool)) (key : Fin keyWidth → Bool)
    (queryCorrect : ∀ record,
      complementedRecordHeader (flatRecords input record) = header →
      Routing.recordKey input record = key ∧ Routing.recordTag input record = true)
    (destination : Fin (networkRecords depth))
    (destinationHeader : complementedRecordHeader (flatRecords
      ((sortedCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) destination) = header)
    (bit : Fin valueWidth) :
    recordValue
      ((sortedCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) destination bit = true ↔
      ∃ source, Routing.recordKey input source = key ∧
        Routing.recordTag input source = false ∧ recordValue input source bit = true := by
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
  rw [sortedCircuit, Circuit.eval_comp, bitonicSortCircuit_eval, recordsCircuit_eval_value]
  change (payloadCircuit depth keyWidth (metadataWidth + valueWidth)
    (Fin.natAdd metadataWidth bit)).eval DeMorgan.interpretation sorted destination = true ↔ _
  rw [payloadCircuit_routesSorted_iff _ sorted
    (bitonicSortBits_keysSorted
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth)) depth true input)
    destination destinationFields.2]
  constructor
  · rintro ⟨source, sameKey, sourceTag, sourceValue⟩
    obtain ⟨originalSource, sameSource⟩ := permuted.rangeContained source
    refine ⟨originalSource, ?_, ?_, ?_⟩
    · exact (congrArg Routing.packedRecordKey sameSource).symm.trans
        (sameKey.trans destinationFields.1)
    · exact (congrArg Routing.packedRecordTag sameSource).symm.trans sourceTag
    · have values := congrArg (fun record => packedRecordValue record bit) sameSource
      exact values.symm.trans sourceValue
  · rintro ⟨originalSource, sameKey, sourceTag, sourceValue⟩
    have reverse : FlatRecordsPermute input sorted := permuted.symm
    obtain ⟨source, sameSource⟩ := reverse.rangeContained originalSource
    refine ⟨source, ?_, ?_, ?_⟩
    · exact (congrArg Routing.packedRecordKey sameSource).symm.trans
        (sameKey.trans destinationFields.1.symm)
    · exact (congrArg Routing.packedRecordTag sameSource).symm.trans sourceTag
    · have values := congrArg (fun record => packedRecordValue record bit) sameSource
      exact values.symm.trans sourceValue

/-- A fixed output position receives the OR of every same-key source bit.
No source uniqueness or existence premise is needed. -/
theorem routingCircuit_fixedOr
    (input : Fin (networkBits depth (recordWidth keyWidth metadataWidth valueWidth)) → Bool)
    (header : Lex (Fin (metadataWidth + 1) → Bool))
    (target : Fin (networkRecords depth)) (key : Fin keyWidth → Bool)
    (uniqueHeader : Semantics.UniqueIndexWhere
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun candidate => candidate = header))
    (rank : (Semantics.matchingIndices
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun candidate => candidate < header)).card = target.val)
    (queryCorrect : ∀ record,
      complementedRecordHeader (flatRecords input record) = header →
      Routing.recordKey input record = key ∧ Routing.recordTag input record = true)
    (bit : Fin valueWidth) :
    recordValue
      ((routingCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) target bit = true ↔
      ∃ source, Routing.recordKey input source = key ∧
        Routing.recordTag input source = false ∧ recordValue input source bit = true := by
  classical
  let values : Fin valueWidth → Bool := fun bit => decide
    (∃ source, Routing.recordKey input source = key ∧
      Routing.recordTag input source = false ∧ recordValue input source bit = true)
  have valuesCorrect : recordValue
      ((routingCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input) target = values := by
    rw [routingCircuit, Circuit.eval_comp, canonicalSortCircuit_eval]
    have permuted := sortedCircuit_headersPermute input
    apply canonicalSort_fixedValue _ header target values
    · exact Semantics.UniqueIndexWhere.of_sequencePermutes permuted uniqueHeader
    · exact (permuted.matchingIndices_card_eq (fun candidate => candidate < header)).trans rank
    · intro record headerMatches
      funext valueBit
      apply Bool.eq_iff_iff.mpr
      rw [show values valueBit = decide
        (∃ source, Routing.recordKey input source = key ∧
          Routing.recordTag input source = false ∧ recordValue input source valueBit = true) from rfl,
        decide_eq_true_eq]
      exact sortedCircuit_valueOr input header key queryCorrect record headerMatches valueBit
  rw [congrFun valuesCorrect bit]
  simp only [values, decide_eq_true_eq]

end Algebraic.MassProduction.Nonuniform.Broadcast
