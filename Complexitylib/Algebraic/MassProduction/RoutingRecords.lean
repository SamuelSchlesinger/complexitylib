/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.RoutingCorrectness

/-!
# Concrete scatter and gather record packing

This module supplies the record-layout layer omitted by the generic routing
primitive.  A record is laid out as `(key, tag, payload)`.  Source records use
tag `false`, destination records use tag `true`, and padding records are
required to use keys outside the active destination-key image.

The key and payload encodings are explicit functions, not typeclass-driven
serializers.  This keeps all finite encodings visible in theorem hypotheses.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Routing

open Sorting
open Sorting.Semantics

/-- Pack one standalone `(key, tag, payload)` record. -/
def packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (payload : Fin payloadWidth -> Bool) :
    Fin (recordWidth keyWidth payloadWidth) -> Bool :=
  Fin.append (Fin.append key (fun _ : Fin 1 => tag)) payload

@[simp] theorem packedRecordKey_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (payload : Fin payloadWidth -> Bool) :
    packedRecordKey (packRecord key tag payload) = key := by
  funext bit
  unfold packedRecordKey packRecord
  rw [show keyBit keyWidth payloadWidth bit =
      Fin.castAdd payloadWidth (Fin.castAdd 1 bit) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Fin.append_left]

@[simp] theorem packedRecordTag_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (payload : Fin payloadWidth -> Bool) :
    packedRecordTag (packRecord key tag payload) = tag := by
  unfold packedRecordTag packRecord
  rw [show tagBit keyWidth payloadWidth =
      Fin.castAdd payloadWidth
        (Fin.natAdd keyWidth (0 : Fin 1)) by
    apply Fin.ext
    rfl]
  rw [Fin.append_left, Fin.append_right]

@[simp] theorem packedRecordPayload_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (payload : Fin payloadWidth -> Bool) :
    packedRecordPayload (packRecord key tag payload) = payload := by
  funext bit
  unfold packedRecordPayload packRecord
  rw [show payloadBit keyWidth payloadWidth bit =
      Fin.natAdd (keyWidth + 1) bit by
    apply Fin.ext
    rfl]
  rw [Fin.append_right]

/-- Concatenate incidence/source records, slot/destination records, and
padding records in a fixed initial layout. -/
def routingRecordSequence
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool) :
    Fin (sourceCount + destinationCount + paddingCount) ->
      Fin (recordWidth keyWidth payloadWidth) -> Bool :=
  Fin.append
    (Fin.append
      (fun source =>
        packRecord (sourceKeys source) false (sourcePayloads source))
      (fun destination =>
        packRecord (destinationKeys destination) true
          (destinationPayloads destination)))
    (fun padding =>
      packRecord (paddingKeys padding) true (paddingPayloads padding))

/-- Routing-namespace compatibility theorem for preserving a unique left
match when a match-free right sequence is appended. -/
theorem UniqueIndexWhere.append_left
    {left : Fin leftCount -> α}
    {right : Fin rightCount -> α}
    {predicate : α -> Prop}
    (uniqueLeft : UniqueIndexWhere left predicate)
    (noneRight : ∀ index, ¬predicate (right index)) :
    UniqueIndexWhere (Fin.append left right) predicate :=
  Sorting.Semantics.UniqueIndexWhere.append_left uniqueLeft noneRight

/-- Routing-namespace compatibility theorem for the symmetric right-match
append rule. -/
theorem UniqueIndexWhere.append_right
    {left : Fin leftCount -> α}
    {right : Fin rightCount -> α}
    {predicate : α -> Prop}
    (noneLeft : ∀ index, ¬predicate (left index))
    (uniqueRight : UniqueIndexWhere right predicate) :
    UniqueIndexWhere (Fin.append left right) predicate :=
  Sorting.Semantics.UniqueIndexWhere.append_right noneLeft uniqueRight

/-- Routing-namespace compatibility theorem for reindexing a unique match
along an equality of lengths. -/
theorem UniqueIndexWhere.cast
    {sequence : Fin leftCount -> α}
    {predicate : α -> Prop}
    (unique : UniqueIndexWhere sequence predicate)
    (countEquality : leftCount = rightCount) :
    UniqueIndexWhere
      (fun index : Fin rightCount =>
        sequence (Fin.cast countEquality.symm index)) predicate :=
  Sorting.Semantics.UniqueIndexWhere.cast unique countEquality

theorem sourceRecordSequence_unique
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (source : Fin sourceCount) :
    UniqueIndexWhere
      (fun index =>
        packRecord (sourceKeys index) false (sourcePayloads index))
      (recordHasKeyTag (sourceKeys source) false) := by
  refine ⟨source, ?_, ?_⟩
  · simp [recordHasKeyTag]
  · intro other otherMatches
    apply sourceKeysInjective
    simpa [recordHasKeyTag] using otherMatches.1

theorem destinationRecordSequence_unique
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (destinationKeysInjective : Function.Injective destinationKeys)
    (destination : Fin destinationCount) :
    UniqueIndexWhere
      (fun index => packRecord (destinationKeys index) true
        (destinationPayloads index))
      (recordHasKeyTag (destinationKeys destination) true) := by
  refine ⟨destination, ?_, ?_⟩
  · simp [recordHasKeyTag]
  · intro other otherMatches
    apply destinationKeysInjective
    simpa [recordHasKeyTag] using otherMatches.1

/-- Every active source key has exactly one source record and exactly one
destination record in the complete initial routing layout.  Injectivity is
requested only of the two active key families; padding records may repeat one
another, but their keys must avoid every active source key. -/
theorem routingRecordSequence_unique_key
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (destinationKeysInjective : Function.Injective destinationKeys)
    (destinationFor : Fin sourceCount -> Fin destinationCount)
    (destinationKey : ∀ source,
      destinationKeys (destinationFor source) = sourceKeys source)
    (paddingAvoids : ∀ padding source,
      paddingKeys padding ≠ sourceKeys source)
    (source : Fin sourceCount) :
    UniqueIndexWhere
        (routingRecordSequence sourceKeys sourcePayloads
          destinationKeys destinationPayloads paddingKeys paddingPayloads)
        (recordHasKeyTag (sourceKeys source) false) ∧
      UniqueIndexWhere
        (routingRecordSequence sourceKeys sourcePayloads
          destinationKeys destinationPayloads paddingKeys paddingPayloads)
        (recordHasKeyTag (sourceKeys source) true) := by
  have uniqueSource := sourceRecordSequence_unique
    sourceKeys sourcePayloads sourceKeysInjective source
  have noDestinationSourceTag : ∀ destination,
      ¬recordHasKeyTag (sourceKeys source) false
        (packRecord (destinationKeys destination) true
          (destinationPayloads destination)) := by
    intro destination
    simp [recordHasKeyTag]
  have noPaddingSourceTag : ∀ padding,
      ¬recordHasKeyTag (sourceKeys source) false
        (packRecord (paddingKeys padding) true
          (paddingPayloads padding)) := by
    intro padding
    simp [recordHasKeyTag]
  have uniqueDestination :
      UniqueIndexWhere
        (fun destination =>
          packRecord (destinationKeys destination) true
            (destinationPayloads destination))
        (recordHasKeyTag (sourceKeys source) true) := by
    simpa only [destinationKey source] using
      destinationRecordSequence_unique destinationKeys
        destinationPayloads destinationKeysInjective
        (destinationFor source)
  have noSourceDestinationTag : ∀ sourceIndex,
      ¬recordHasKeyTag (sourceKeys source) true
        (packRecord (sourceKeys sourceIndex) false
          (sourcePayloads sourceIndex)) := by
    intro sourceIndex
    simp [recordHasKeyTag]
  have noPaddingDestinationKey : ∀ padding,
      ¬recordHasKeyTag (sourceKeys source) true
        (packRecord (paddingKeys padding) true
          (paddingPayloads padding)) := by
    intro padding matching
    exact paddingAvoids padding source
      (by simpa [recordHasKeyTag] using matching.1)
  constructor
  · unfold routingRecordSequence
    exact (uniqueSource.append_left noDestinationSourceTag).append_left
      noPaddingSourceTag
  · unfold routingRecordSequence
    exact (UniqueIndexWhere.append_right noSourceDestinationTag
      uniqueDestination).append_left noPaddingDestinationKey

/-- Every destination key is unique in the complete layout independently of
whether a matching source with that key exists. -/
theorem routingRecordSequence_unique_destination
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (destinationKeysInjective : Function.Injective destinationKeys)
    (paddingAvoidsDestination : forall padding destination,
      paddingKeys padding ≠ destinationKeys destination)
    (destination : Fin destinationCount) :
    UniqueIndexWhere
      (routingRecordSequence sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads)
      (recordHasKeyTag (destinationKeys destination) true) := by
  have noSource : forall source,
      Not (recordHasKeyTag (destinationKeys destination) true
        (packRecord (sourceKeys source) false (sourcePayloads source))) := by
    intro source
    simp [recordHasKeyTag]
  have uniqueDestination := destinationRecordSequence_unique
    destinationKeys destinationPayloads destinationKeysInjective destination
  have noPadding : forall padding,
      Not (recordHasKeyTag (destinationKeys destination) true
        (packRecord (paddingKeys padding) true
          (paddingPayloads padding))) := by
    intro padding matching
    exact paddingAvoidsDestination padding destination
      (by simpa [recordHasKeyTag] using matching.1)
  unfold routingRecordSequence
  exact (UniqueIndexWhere.append_right noSource
    uniqueDestination).append_left noPadding

/-- Every source key is unique in the complete layout whenever the source-key
family is injective.  Destination and padding keys are irrelevant because
their tag is different. -/
theorem routingRecordSequence_unique_source
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (source : Fin sourceCount) :
    UniqueIndexWhere
      (routingRecordSequence sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads)
      (recordHasKeyTag (sourceKeys source) false) := by
  have uniqueSource := sourceRecordSequence_unique sourceKeys sourcePayloads
    sourceKeysInjective source
  have noDestination : forall destination,
      Not (recordHasKeyTag (sourceKeys source) false
        (packRecord (destinationKeys destination) true
          (destinationPayloads destination))) := by
    intro destination
    simp [recordHasKeyTag]
  have noPadding : forall padding,
      Not (recordHasKeyTag (sourceKeys source) false
        (packRecord (paddingKeys padding) true
          (paddingPayloads padding))) := by
    intro padding
    simp [recordHasKeyTag]
  unfold routingRecordSequence
  exact (uniqueSource.append_left noDestination).append_left noPadding

/-! ## Exact network-capacity padding -/

/-- Position occupied by a source record in the unpadded semantic layout. -/
def routingSourceIndex
    (source : Fin sourceCount) :
    Fin (sourceCount + destinationCount + paddingCount) :=
  Fin.castAdd paddingCount (Fin.castAdd destinationCount source)

/-- Position occupied by a destination record in the unpadded semantic
routing layout. -/
def routingDestinationIndex
    (destination : Fin destinationCount) :
    Fin (sourceCount + destinationCount + paddingCount) :=
  Fin.castAdd paddingCount (Fin.natAdd sourceCount destination)

/-- Position occupied by a padding record in the semantic routing layout. -/
def routingPaddingIndex
    (padding : Fin paddingCount) :
    Fin (sourceCount + destinationCount + paddingCount) :=
  Fin.natAdd (sourceCount + destinationCount) padding

@[simp] theorem routingRecordSequence_source
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (source : Fin sourceCount) :
    routingRecordSequence sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads
        (routingSourceIndex (destinationCount := destinationCount)
          (paddingCount := paddingCount) source) =
      packRecord (sourceKeys source) false (sourcePayloads source) := by
  simp [routingRecordSequence, routingSourceIndex]

@[simp] theorem routingRecordSequence_destination
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (destination : Fin destinationCount) :
    routingRecordSequence sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads
        (routingDestinationIndex (sourceCount := sourceCount)
          (paddingCount := paddingCount) destination) =
      packRecord (destinationKeys destination) true
        (destinationPayloads destination) := by
  simp [routingRecordSequence, routingDestinationIndex]

@[simp] theorem routingRecordSequence_padding
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (padding : Fin paddingCount) :
    routingRecordSequence sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads
        (routingPaddingIndex (sourceCount := sourceCount)
          (destinationCount := destinationCount) padding) =
      packRecord (paddingKeys padding) true
        (paddingPayloads padding) := by
  simp [routingRecordSequence, routingPaddingIndex]

/-- Reindex an exactly padded semantic routing layout to the power-of-two
record count consumed by the sorting network. -/
def networkRoutingRecords
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth) :
    Fin (networkRecords depth) ->
      Fin (recordWidth keyWidth payloadWidth) -> Bool :=
  fun record =>
    routingRecordSequence sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads
      (Fin.cast recordCount.symm record)

/-- The source's position after the exact-capacity cast. -/
def networkRoutingSourceIndex
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (source : Fin sourceCount) : Fin (networkRecords depth) :=
  Fin.cast recordCount
    (routingSourceIndex (destinationCount := destinationCount)
      (paddingCount := paddingCount) source)

/-- The destination's position after the exact-capacity cast. -/
def networkRoutingDestinationIndex
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (destination : Fin destinationCount) : Fin (networkRecords depth) :=
  Fin.cast recordCount
    (routingDestinationIndex (sourceCount := sourceCount)
      (paddingCount := paddingCount) destination)

/-- The padding record's position after the exact-capacity cast. -/
def networkRoutingPaddingIndex
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (padding : Fin paddingCount) : Fin (networkRecords depth) :=
  Fin.cast recordCount
    (routingPaddingIndex (sourceCount := sourceCount)
      (destinationCount := destinationCount) padding)

@[simp] theorem networkRoutingRecords_source
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (source : Fin sourceCount) :
    networkRoutingRecords sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount
        (networkRoutingSourceIndex recordCount source) =
      packRecord (sourceKeys source) false (sourcePayloads source) := by
  unfold networkRoutingRecords networkRoutingSourceIndex
  exact routingRecordSequence_source sourceKeys sourcePayloads
    destinationKeys destinationPayloads paddingKeys paddingPayloads source

@[simp] theorem networkRoutingRecords_destination
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (destination : Fin destinationCount) :
    networkRoutingRecords sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount
        (networkRoutingDestinationIndex recordCount destination) =
      packRecord (destinationKeys destination) true
        (destinationPayloads destination) := by
  unfold networkRoutingRecords networkRoutingDestinationIndex
  exact routingRecordSequence_destination sourceKeys sourcePayloads
    destinationKeys destinationPayloads paddingKeys paddingPayloads
    destination

@[simp] theorem networkRoutingRecords_padding
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (padding : Fin paddingCount) :
    networkRoutingRecords sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount
        (networkRoutingPaddingIndex recordCount padding) =
      packRecord (paddingKeys padding) true
        (paddingPayloads padding) := by
  unfold networkRoutingRecords networkRoutingPaddingIndex
  exact routingRecordSequence_padding sourceKeys sourcePayloads
    destinationKeys destinationPayloads paddingKeys paddingPayloads padding

/-! ## Flattening semantic records into sorter input wires -/

/-- Row-major bit packing of an already constructed record sequence. -/
def recordArrayBits
    (records : Fin (networkRecords depth) -> Fin packedWidth -> Bool) :
    Fin (networkBits depth packedWidth) -> Bool :=
  fun flat =>
    let recordAndBit :=
      (finProdFinEquiv (m := networkRecords depth) (n := packedWidth)).symm flat
    records recordAndBit.1 recordAndBit.2

/-- Flattening and then reading by records is an exact round trip. -/
@[simp] theorem flatRecords_recordArrayBits
    (records : Fin (networkRecords depth) -> Fin packedWidth -> Bool) :
    flatRecords (recordArrayBits records) = records := by
  funext record bit
  unfold flatRecords networkRecord recordArrayBits
  rw [Equiv.symm_apply_apply]

/-- Fully packed bit input for one exactly padded routing network. -/
def routingInputBits
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth) :
    Fin (networkBits depth (recordWidth keyWidth payloadWidth)) -> Bool :=
  recordArrayBits
    (networkRoutingRecords sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads recordCount)

@[simp] theorem flatRecords_routingInputBits
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth) :
    flatRecords
        (routingInputBits sourceKeys sourcePayloads destinationKeys
          destinationPayloads paddingKeys paddingPayloads recordCount) =
      networkRoutingRecords sourceKeys sourcePayloads destinationKeys
        destinationPayloads paddingKeys paddingPayloads recordCount := by
  simp [routingInputBits]

/-- Every packed destination remains uniquely identifiable after exact
capacity padding and flattening, even when no source uses its key. -/
theorem routingInputBits_unique_destination
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (destinationKeysInjective : Function.Injective destinationKeys)
    (paddingAvoidsDestination : forall padding destination,
      paddingKeys padding ≠ destinationKeys destination)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (destination : Fin destinationCount) :
    let input := routingInputBits sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads recordCount
    UniqueIndexWhere (flatRecords input)
      (recordHasKeyTag (destinationKeys destination) true) := by
  dsimp only
  rw [flatRecords_routingInputBits]
  exact (routingRecordSequence_unique_destination sourceKeys sourcePayloads
    destinationKeys destinationPayloads paddingKeys paddingPayloads
    destinationKeysInjective paddingAvoidsDestination destination).cast
      recordCount

/-- Exact-capacity packing retains uniqueness of every source record. -/
theorem routingInputBits_unique_source
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (source : Fin sourceCount) :
    let input := routingInputBits sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads recordCount
    UniqueIndexWhere (flatRecords input)
      (recordHasKeyTag (sourceKeys source) false) := by
  dsimp only
  rw [flatRecords_routingInputBits]
  exact (routingRecordSequence_unique_source sourceKeys sourcePayloads
    destinationKeys destinationPayloads paddingKeys paddingPayloads
    sourceKeysInjective source).cast recordCount

/-- The packed sorter input retains the unique source/destination invariant
proved for the semantic record layout. -/
theorem routingInputBits_unique_key
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (destinationKeysInjective : Function.Injective destinationKeys)
    (destinationFor : Fin sourceCount -> Fin destinationCount)
    (destinationKey : ∀ source,
      destinationKeys (destinationFor source) = sourceKeys source)
    (paddingAvoids : ∀ padding source,
      paddingKeys padding ≠ sourceKeys source)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (source : Fin sourceCount) :
    let input := routingInputBits sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads recordCount
    UniqueIndexWhere (flatRecords input)
        (recordHasKeyTag (sourceKeys source) false) ∧
      UniqueIndexWhere (flatRecords input)
        (recordHasKeyTag (sourceKeys source) true) := by
  dsimp only
  rw [flatRecords_routingInputBits]
  exact And.imp (fun unique => unique.cast recordCount)
    (fun unique => unique.cast recordCount)
    (routingRecordSequence_unique_key sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      sourceKeysInjective destinationKeysInjective destinationFor
      destinationKey paddingAvoids source)

/-- End-to-end scatter correctness for the concrete record layout.  For every
active source, the actual sorting-and-predecessor-copy circuit produces the
source payload at the uniquely keyed destination record. -/
theorem routingInputBits_routes_source_payload
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationPayloads : Fin destinationCount ->
      Fin payloadWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (destinationKeysInjective : Function.Injective destinationKeys)
    (destinationFor : Fin sourceCount -> Fin destinationCount)
    (destinationKey : ∀ source,
      destinationKeys (destinationFor source) = sourceKeys source)
    (paddingAvoids : ∀ padding source,
      paddingKeys padding ≠ sourceKeys source)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (source : Fin sourceCount) :
    let input := routingInputBits sourceKeys sourcePayloads destinationKeys
      destinationPayloads paddingKeys paddingPayloads recordCount
    let sorted := bitonicSortBits
      (keyAndTagFitsRecord keyWidth payloadWidth) depth true input
    ∃ destinationSorted,
      recordHasKeyTag (sourceKeys source) true
          (flatRecords sorted destinationSorted) ∧
        recordPayload
            ((sortedPredecessorCopyCircuit depth keyWidth payloadWidth
              false true).eval DeMorgan.interpretation input)
            destinationSorted =
          sourcePayloads source := by
  dsimp only
  let input := routingInputBits sourceKeys sourcePayloads destinationKeys
    destinationPayloads paddingKeys paddingPayloads recordCount
  have uniquePair :
      UniqueIndexWhere (flatRecords input)
          (recordHasKeyTag (sourceKeys source) false) ∧
        UniqueIndexWhere (flatRecords input)
          (recordHasKeyTag (sourceKeys source) true) := by
    simpa only [input] using routingInputBits_unique_key sourceKeys
      sourcePayloads destinationKeys destinationPayloads paddingKeys
      paddingPayloads sourceKeysInjective destinationKeysInjective
      destinationFor destinationKey paddingAvoids recordCount source
  obtain ⟨sourceInput, sourceSorted, destinationSorted,
      sourceInputMatches, _sourceSortedMatches, destinationSortedMatches,
      routedPayload⟩ :=
    sortedPredecessorCopyCircuit_routes_unique_key input
      (sourceKeys source) uniquePair.1 uniquePair.2
  let expectedSource := networkRoutingSourceIndex recordCount source
  have expectedRecord :
      flatRecords input expectedSource =
        packRecord (sourceKeys source) false (sourcePayloads source) := by
    simp only [input, flatRecords_routingInputBits]
    exact networkRoutingRecords_source sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      recordCount source
  have expectedMatches :
      recordHasKeyTag (sourceKeys source) false
        (flatRecords input expectedSource) := by
    rw [expectedRecord]
    simp [recordHasKeyTag]
  obtain ⟨uniqueSourceIndex, _uniqueSourceMatches, sourceOnly⟩ :=
    uniquePair.1
  have sourceInputIndex := sourceOnly sourceInput sourceInputMatches
  have expectedSourceIndex := sourceOnly expectedSource expectedMatches
  have sourceInputEq : sourceInput = expectedSource :=
    sourceInputIndex.trans expectedSourceIndex.symm
  have sourcePayloadAtInput :
      packedRecordPayload (flatRecords input sourceInput) =
        sourcePayloads source := by
    rw [sourceInputEq, expectedRecord]
    simp
  exact ⟨destinationSorted, destinationSortedMatches,
    routedPayload.trans sourcePayloadAtInput⟩

end Routing
end MassProduction
end Algebraic
