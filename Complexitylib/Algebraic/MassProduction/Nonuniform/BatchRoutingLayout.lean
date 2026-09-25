/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchRouting

/-!
# Batched lookup in the concrete routing layout

Only source keys must be injective. Repeated queries and padding records
with active keys are allowed: their preserved metadata distinguishes them
when the output order is restored.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting RoutingMetadata CanonicalMetadataRouting

/-- The existing packed layout supports repeated lookup requests through the
shared broadcast circuit, without any uniqueness premise on query keys. -/
theorem routingCircuit_layoutValue
    (destinationFits : destinationCount ≤ 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount → Fin keyWidth → Bool)
    (sourceMetadata : Fin sourceCount → Fin (orderWidth + 1) → Bool)
    (sourceValues : Fin sourceCount → Fin valueWidth → Bool)
    (destinationKeys : Fin destinationCount → Fin keyWidth → Bool)
    (destinationValues : Fin destinationCount → Fin valueWidth → Bool)
    (paddingKeys : Fin paddingCount → Fin keyWidth → Bool)
    (paddingTails : Fin paddingCount → Fin orderWidth → Bool)
    (paddingValues : Fin paddingCount → Fin valueWidth → Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (sourceFor : Fin destinationCount → Fin sourceCount)
    (matchingKey : ∀ destination, sourceKeys (sourceFor destination) = destinationKeys destination)
    (recordCount : sourceCount + destinationCount + paddingCount = networkRecords depth)
    (target : Fin destinationCount) :
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
      (Fin.castLE (by omega : destinationCount ≤ networkRecords depth) target) =
        sourceValues (sourceFor target) := by
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
  have uniqueSource : Semantics.UniqueIndexWhere (flatRecords input)
      (Routing.recordHasKeyTag (destinationKeys target) false) := by
    simpa only [matchingKey target] using
      Routing.routingInputBits_unique_source sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads sourceKeysInjective recordCount (sourceFor target)
  let expectedSource := Routing.networkRoutingSourceIndex recordCount (sourceFor target)
  have expectedSourceRecord : flatRecords input expectedSource =
      packRecord (sourceKeys (sourceFor target)) false (sourceMetadata (sourceFor target))
        (sourceValues (sourceFor target)) := by
    change flatRecords input expectedSource =
      Routing.packRecord (sourceKeys (sourceFor target)) false (sourcePayloads (sourceFor target))
    simp only [input, Routing.flatRecords_routingInputBits]
    exact Routing.networkRoutingRecords_source sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads recordCount (sourceFor target)
  have expectedSourceMatches : Routing.recordHasKeyTag (destinationKeys target) false
      (flatRecords input expectedSource) := by
    rw [expectedSourceRecord]
    simp [Routing.recordHasKeyTag, matchingKey target]
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
  apply routingCircuit_fixedValue input header _ (destinationKeys target)
    (sourceValues (sourceFor target)) uniqueHeader
  · exact routingInputBits_orderHeader_count_lt destinationFits sourceKeys sourceMetadata
      sourceValues destinationKeys destinationValues paddingKeys paddingTails paddingValues recordCount target
  · exact uniqueSource
  · intro record keyCorrect tagCorrect
    obtain ⟨uniqueIndex, _, only⟩ := uniqueSource
    have equalSource : record = expectedSource :=
      (only record ((Routing.recordHasKeyTag_flatRecords_iff input record
        (destinationKeys target) false).mpr ⟨keyCorrect, tagCorrect⟩)).trans
        (only expectedSource expectedSourceMatches).symm
    change packedRecordValue (flatRecords input record) = _
    rw [equalSource, expectedSourceRecord, packedRecordValue_packRecord]
  · intro record headerMatches
    obtain ⟨uniqueIndex, _, only⟩ := uniqueHeader
    have equalDestination : record = expectedDestination :=
      (only record headerMatches).trans (only expectedDestination expectedDestinationMatches).symm
    change Routing.packedRecordKey (flatRecords input record) = _ ∧
      Routing.packedRecordTag (flatRecords input record) = _
    rw [equalDestination, expectedDestinationRecord]
    simp

end Algebraic.MassProduction.Nonuniform.Broadcast
