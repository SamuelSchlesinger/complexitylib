/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchOr
public import Complexitylib.Algebraic.MassProduction.Nonuniform.RoutingSources

/-!
# OR aggregation in the concrete routing layout

Each destination receives the disjunction of all matching source values.
Repeated source keys, repeated queries, and absent keys are all allowed.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting RoutingMetadata CanonicalMetadataRouting

/-- The packed router computes a batched Boolean OR, in literal query order. -/
theorem routingCircuit_layoutOr
    (destinationFits : destinationCount ≤ 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount → Fin keyWidth → Bool)
    (sourceMetadata : Fin sourceCount → Fin (orderWidth + 1) → Bool)
    (sourceValues : Fin sourceCount → Fin valueWidth → Bool)
    (destinationKeys : Fin destinationCount → Fin keyWidth → Bool)
    (destinationValues : Fin destinationCount → Fin valueWidth → Bool)
    (paddingKeys : Fin paddingCount → Fin keyWidth → Bool)
    (paddingTails : Fin paddingCount → Fin orderWidth → Bool)
    (paddingValues : Fin paddingCount → Fin valueWidth → Bool)
    (recordCount : sourceCount + destinationCount + paddingCount = networkRecords depth)
    (target : Fin destinationCount) (bit : Fin valueWidth) :
    let input := Routing.routingInputBits sourceKeys
      (fun source => Fin.append (sourceMetadata source) (sourceValues source))
      destinationKeys
      (fun destination => Fin.append
        (destinationOrderMetadata destinationFits destination) (destinationValues destination))
      paddingKeys
      (fun padding => Fin.append (paddingRoutingKey (paddingTails padding)) (paddingValues padding))
      recordCount
    recordValue
      ((routingCircuit depth keyWidth (orderWidth + 1) valueWidth).eval
        DeMorgan.interpretation input)
      (Fin.castLE (by omega : destinationCount ≤ networkRecords depth) target) bit = true ↔
        ∃ source, sourceKeys source = destinationKeys target ∧ sourceValues source bit = true := by
  dsimp only
  let sourcePayloads := fun source => Fin.append (sourceMetadata source) (sourceValues source)
  let destinationPayloads := fun destination => Fin.append
    (destinationOrderMetadata destinationFits destination) (destinationValues destination)
  let paddingPayloads := fun padding => Fin.append
    (paddingRoutingKey (paddingTails padding)) (paddingValues padding)
  let input := Routing.routingInputBits sourceKeys sourcePayloads destinationKeys
    destinationPayloads paddingKeys paddingPayloads recordCount
  let header := CanonicalRouting.activeDestinationHeader
    (lexBitVectorAt (Fin.castLE destinationFits target))
  have uniqueHeader : Semantics.UniqueIndexWhere
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun candidate => candidate = header) :=
    routingInputBits_unique_order_header destinationFits sourceKeys sourceMetadata
      sourceValues destinationKeys destinationValues paddingKeys paddingTails paddingValues recordCount target
  let expectedDestination := Routing.networkRoutingDestinationIndex recordCount target
  have expectedDestinationRecord : flatRecords input expectedDestination =
      packRecord (destinationKeys target) true (destinationOrderMetadata destinationFits target)
        (destinationValues target) := by
    change flatRecords input expectedDestination =
      Routing.packRecord (destinationKeys target) true (destinationPayloads target)
    simp only [input, Routing.flatRecords_routingInputBits]
    exact Routing.networkRoutingRecords_destination sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads recordCount target
  have expectedDestinationMatches :
      complementedRecordHeader (flatRecords input expectedDestination) = header := by
    rw [expectedDestinationRecord]
    simp [header, destinationOrderMetadata, CanonicalRouting.activeDestinationHeader]
  have queryCorrect : ∀ record,
      complementedRecordHeader (flatRecords input record) = header →
      Routing.recordKey input record = destinationKeys target ∧ Routing.recordTag input record = true := by
    intro record headerMatches
    obtain ⟨uniqueIndex, _, only⟩ := uniqueHeader
    have equalDestination : record = expectedDestination :=
      (only record headerMatches).trans (only expectedDestination expectedDestinationMatches).symm
    change Routing.packedRecordKey (flatRecords input record) = _ ∧
      Routing.packedRecordTag (flatRecords input record) = _
    rw [equalDestination, expectedDestinationRecord]
    simp
  rw [routingCircuit_fixedOr input header _ (destinationKeys target) uniqueHeader
    (routingInputBits_orderHeader_count_lt destinationFits sourceKeys sourceMetadata
      sourceValues destinationKeys destinationValues paddingKeys paddingTails paddingValues recordCount target)
    queryCorrect bit]
  constructor
  · rintro ⟨record, sameKey, sourceTag, sourceValue⟩
    obtain ⟨source, sameRecord⟩ := routingInputBits_sourceOfTag sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads recordCount record sourceTag
    have sourceRecord : flatRecords input record =
        packRecord (sourceKeys source) false (sourceMetadata source) (sourceValues source) := sameRecord
    change Routing.packedRecordKey (flatRecords input record) = _ at sameKey
    change packedRecordValue (flatRecords input record) bit = true at sourceValue
    rw [sourceRecord, packedRecordKey_packRecord] at sameKey
    rw [sourceRecord, packedRecordValue_packRecord] at sourceValue
    exact ⟨source, sameKey, sourceValue⟩
  · rintro ⟨source, sameKey, sourceValue⟩
    let index := Routing.networkRoutingSourceIndex recordCount source
    have sourceRecord : flatRecords input index =
        packRecord (sourceKeys source) false (sourceMetadata source) (sourceValues source) := by
      change flatRecords input index = Routing.packRecord (sourceKeys source) false (sourcePayloads source)
      simp only [input, Routing.flatRecords_routingInputBits]
      exact Routing.networkRoutingRecords_source sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount source
    refine ⟨index, ?_, ?_, ?_⟩
    · change Routing.packedRecordKey (flatRecords input index) = _
      rw [sourceRecord, packedRecordKey_packRecord]
      exact sameKey
    · change Routing.packedRecordTag (flatRecords input index) = _
      rw [sourceRecord, packedRecordTag_packRecord]
    · change packedRecordValue (flatRecords input index) bit = true
      rw [sourceRecord, packedRecordValue_packRecord]
      exact sourceValue

end Algebraic.MassProduction.Nonuniform.Broadcast
