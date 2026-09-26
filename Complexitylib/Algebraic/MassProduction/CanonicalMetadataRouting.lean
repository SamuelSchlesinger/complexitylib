/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.RoutingMetadata

/-!
# Canonical ordering by preserved routing metadata

After gather matching, destination records must be ordered by their preserved
`(request, line position)` metadata rather than by the `(group, point)` key
used for matching.  This module constructs the free within-record
permutation selecting `(tag, metadata)` as the second sort key, preceded by
the same explicit tag-complement pass used for scatter.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace CanonicalMetadataRouting

open CanonicalRouting
open RoutingMetadata
open Sorting

/-- Forward block swap taking virtual `(tag, metadata, matching key, value)`
positions to physical `(matching key, tag, metadata, value)` positions. -/
def metadataOrderForward
    (keyWidth metadataWidth valueWidth : Nat)
    (bit : Fin (recordWidth keyWidth metadataWidth valueWidth)) :
    Fin (recordWidth keyWidth metadataWidth valueWidth) :=
  if header : bit.val < metadataWidth + 1 then
    ⟨keyWidth + bit.val, by
      unfold recordWidth Routing.recordWidth
      omega⟩
  else if matchingKey : bit.val < metadataWidth + 1 + keyWidth then
    ⟨bit.val - (metadataWidth + 1), by
      unfold recordWidth Routing.recordWidth
      omega⟩
  else
    bit

/-- Inverse physical-to-virtual block swap. -/
def metadataOrderBackward
    (keyWidth metadataWidth valueWidth : Nat)
    (bit : Fin (recordWidth keyWidth metadataWidth valueWidth)) :
    Fin (recordWidth keyWidth metadataWidth valueWidth) :=
  if matchingKey : bit.val < keyWidth then
    ⟨metadataWidth + 1 + bit.val, by
      unfold recordWidth Routing.recordWidth
      omega⟩
  else if header : bit.val < keyWidth + (metadataWidth + 1) then
    ⟨bit.val - keyWidth, by
      unfold recordWidth Routing.recordWidth
      omega⟩
  else
    bit

/-- Permutation swapping the matching-key and `(tag, metadata)` blocks while
leaving the copied-value block fixed. -/
def metadataOrderBitOrder
    (keyWidth metadataWidth valueWidth : Nat) :
    Equiv.Perm (Fin (recordWidth keyWidth metadataWidth valueWidth)) where
  toFun := metadataOrderForward keyWidth metadataWidth valueWidth
  invFun := metadataOrderBackward keyWidth metadataWidth valueWidth
  left_inv bit := by
    unfold metadataOrderForward
    by_cases header : bit.val < metadataWidth + 1
    · rw [dite_eq_left header]
      unfold metadataOrderBackward
      have notMatchingKey :
          Not (keyWidth + bit.val < keyWidth) := by omega
      have inHeader :
          keyWidth + bit.val < keyWidth + (metadataWidth + 1) := by omega
      rw [dite_eq_right notMatchingKey, dite_eq_left inHeader]
      apply Fin.ext
      simp
    · rw [dite_eq_right header]
      by_cases matchingKey : bit.val < metadataWidth + 1 + keyWidth
      · rw [dite_eq_left matchingKey]
        unfold metadataOrderBackward
        have inMatchingKey :
            bit.val - (metadataWidth + 1) < keyWidth := by omega
        rw [dite_eq_left inMatchingKey]
        apply Fin.ext
        simp
        omega
      · rw [dite_eq_right matchingKey]
        unfold metadataOrderBackward
        have notPhysicalKey : Not (bit.val < keyWidth) := by omega
        have notPhysicalHeader :
            Not (bit.val < keyWidth + (metadataWidth + 1)) := by omega
        rw [dite_eq_right notPhysicalKey, dite_eq_right notPhysicalHeader]
  right_inv bit := by
    unfold metadataOrderBackward
    by_cases matchingKey : bit.val < keyWidth
    · rw [dite_eq_left matchingKey]
      unfold metadataOrderForward
      have notVirtualHeader :
          Not (metadataWidth + 1 + bit.val < metadataWidth + 1) := by
        omega
      have inVirtualKey :
          metadataWidth + 1 + bit.val < metadataWidth + 1 + keyWidth := by
        omega
      rw [dite_eq_right notVirtualHeader, dite_eq_left inVirtualKey]
      apply Fin.ext
      simp
    · rw [dite_eq_right matchingKey]
      by_cases header : bit.val < keyWidth + (metadataWidth + 1)
      · rw [dite_eq_left header]
        unfold metadataOrderForward
        have inVirtualHeader : bit.val - keyWidth < metadataWidth + 1 := by
          omega
        rw [dite_eq_left inVirtualHeader]
        apply Fin.ext
        simp
        omega
      · rw [dite_eq_right header]
        unfold metadataOrderForward
        have notVirtualHeader :
            Not (bit.val < metadataWidth + 1) := by omega
        have notVirtualKey :
            Not (bit.val < metadataWidth + 1 + keyWidth) := by omega
        rw [dite_eq_right notVirtualHeader, dite_eq_right notVirtualKey]

theorem metadataOrderKeyFits
    (keyWidth metadataWidth valueWidth : Nat) :
    metadataWidth + 1 <= recordWidth keyWidth metadataWidth valueWidth := by
  unfold recordWidth Routing.recordWidth
  omega

/-- A virtual `(tag, metadata)` bit maps to the corresponding physical bit
after the matching-key block. -/
theorem metadataOrderBitOrder_prefix
    (bit : Fin (metadataWidth + 1)) :
    metadataOrderBitOrder keyWidth metadataWidth valueWidth
        (Fin.castLE
          (metadataOrderKeyFits keyWidth metadataWidth valueWidth) bit) =
      ⟨keyWidth + bit.val, by
        unfold recordWidth Routing.recordWidth
        omega⟩ := by
  unfold metadataOrderBitOrder metadataOrderForward
  change (if header : bit.val < metadataWidth + 1 then
      (⟨keyWidth + bit.val, by
        unfold recordWidth Routing.recordWidth
        omega⟩ : Fin (recordWidth keyWidth metadataWidth valueWidth))
    else if matchingKey : bit.val < metadataWidth + 1 + keyWidth then
      ⟨bit.val - (metadataWidth + 1), by
        unfold recordWidth Routing.recordWidth
        omega⟩
    else Fin.castLE
      (metadataOrderKeyFits keyWidth metadataWidth valueWidth) bit) = _
  rw [dite_eq_left bit.isLt]

/-- The selected virtual prefix is exactly the complemented physical tag
followed by the preserved metadata field. -/
theorem metadataOrderVirtualKey
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    flatRecordKey
        (metadataOrderKeyFits keyWidth metadataWidth valueWidth)
        (flatRecords
          (reindexRecordBits
            (metadataOrderBitOrder keyWidth metadataWidth valueWidth) input)
          record) =
      toLex (Fin.cons (Routing.recordTag input record)
        (recordMetadata input record)) := by
  unfold flatRecordKey
  rw [toLex_inj]
  funext bit
  rw [flatRecords_reindexRecordBits]
  change flatRecords input record
      (metadataOrderBitOrder keyWidth metadataWidth valueWidth
        (Fin.castLE
          (metadataOrderKeyFits keyWidth metadataWidth valueWidth) bit)) = _
  rw [metadataOrderBitOrder_prefix]
  refine Fin.cases ?_ (fun metadataBitIndex => ?_) bit
  · unfold Routing.recordTag
    apply congrArg input
    apply Fin.ext
    rfl
  · unfold recordMetadata
    apply congrArg input
    apply Fin.ext
    unfold Routing.recordBitIndex metadataBit Routing.payloadBit
    simp [finProdFinEquiv]
    omega

/-- Flip tags and canonically order complete records by `(tag, metadata)`. -/
def canonicalSortBits
    (depth keyWidth metadataWidth valueWidth : Nat)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool :=
  bitonicSortByBits
    (metadataOrderBitOrder keyWidth metadataWidth valueWidth)
    (metadataOrderKeyFits keyWidth metadataWidth valueWidth) depth true
    (complementRoutingTagsBits depth keyWidth
      (metadataWidth + valueWidth) input)

/-- Explicit tag-flip and metadata-ordering circuit. -/
def canonicalSortCircuit
    (depth keyWidth metadataWidth valueWidth : Nat) :=
  (bitonicSortByCircuit
      (metadataOrderBitOrder keyWidth metadataWidth valueWidth)
      (metadataOrderKeyFits keyWidth metadataWidth valueWidth) depth true).comp
    (complementRoutingTagsCircuit depth keyWidth
      (metadataWidth + valueWidth))

/-- The exact gate count of `canonicalSortCircuit`. -/
@[simp] theorem canonicalSortCircuit_size
    (depth keyWidth metadataWidth valueWidth : Nat) :
    (canonicalSortCircuit depth keyWidth metadataWidth valueWidth).size =
      ∑ output :
          Fin
            (networkBits depth
              (Routing.recordWidth keyWidth (metadataWidth + valueWidth))),
          complementTagOutputGateCount depth keyWidth (metadataWidth + valueWidth)
            output +
        bitonicSortGateCount
          (metadataOrderKeyFits keyWidth metadataWidth valueWidth) depth := by
  simp [canonicalSortCircuit]

@[simp] theorem canonicalSortCircuit_eval
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    (canonicalSortCircuit depth keyWidth metadataWidth valueWidth).eval
        DeMorgan.interpretation input =
      canonicalSortBits depth keyWidth metadataWidth valueWidth input := by
  rw [canonicalSortCircuit, Circuit.eval_comp,
    bitonicSortByCircuit_eval, complementRoutingTagsCircuit_eval]
  rfl

theorem canonicalSortBits_recordsPermute
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    FlatRecordsPermute
      (canonicalSortBits depth keyWidth metadataWidth valueWidth input)
      (complementRoutingTagsBits depth keyWidth
        (metadataWidth + valueWidth) input) := by
  exact bitonicSortByBits_recordsPermute
    (metadataOrderBitOrder keyWidth metadataWidth valueWidth)
    (metadataOrderKeyFits keyWidth metadataWidth valueWidth) depth true _

theorem canonicalSortBits_keysSorted
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    FlatKeysSortedBy
      (metadataOrderBitOrder keyWidth metadataWidth valueWidth)
      (metadataOrderKeyFits keyWidth metadataWidth valueWidth) true
      (canonicalSortBits depth keyWidth metadataWidth valueWidth input) := by
  exact bitonicSortByBits_keysSorted
    (metadataOrderBitOrder keyWidth metadataWidth valueWidth)
    (metadataOrderKeyFits keyWidth metadataWidth valueWidth) depth true _

theorem canonicalSortCircuit_cost_le :
    (canonicalSortCircuit depth keyWidth metadataWidth valueWidth).cost
        DeMorgan.standardCost <=
      networkBits depth (recordWidth keyWidth metadataWidth valueWidth) +
        depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth metadataWidth valueWidth) *
            (2 * ((metadataWidth + 1) *
              (6 * (metadataWidth + 1) + 4)) + 4)) := by
  rw [canonicalSortCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (complementRoutingTagsCircuit_cost_le
      (depth := depth) (keyWidth := keyWidth)
      (payloadWidth := metadataWidth + valueWidth))
    (bitonicSortByCircuit_cost_le
      (metadataOrderBitOrder keyWidth metadataWidth valueWidth)
      (metadataOrderKeyFits keyWidth metadataWidth valueWidth) depth true)

/-! ## Complete gather-match and canonical-order pipeline -/

/-- Canonical `(tag, metadata)` header of a standalone record. -/
def recordHeader
    (record : Fin (recordWidth keyWidth metadataWidth valueWidth) -> Bool) :
    Lex (Fin (metadataWidth + 1) -> Bool) :=
  toLex (Fin.cons (Routing.packedRecordTag record)
    (packedRecordMetadata record))

/-- Metadata header after complementing the record tag. -/
def complementedRecordHeader
    (record : Fin (recordWidth keyWidth metadataWidth valueWidth) -> Bool) :
    Lex (Fin (metadataWidth + 1) -> Bool) :=
  toLex (Fin.cons (!(Routing.packedRecordTag record))
    (packedRecordMetadata record))

@[simp] theorem recordMetadata_complementRoutingTagsBits
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordMetadata
        (complementRoutingTagsBits depth keyWidth
          (metadataWidth + valueWidth) input) record =
      recordMetadata input record := by
  funext bit
  have preserved := congrFun
    (CanonicalRouting.complementRoutingTagsBits_recordPayload input record)
    (Fin.castAdd valueWidth bit)
  exact preserved

@[simp] theorem recordValue_complementRoutingTagsBits
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordValue
        (complementRoutingTagsBits depth keyWidth
          (metadataWidth + valueWidth) input) record =
      recordValue input record := by
  funext bit
  have preserved := congrFun
    (CanonicalRouting.complementRoutingTagsBits_recordPayload input record)
    (Fin.natAdd metadataWidth bit)
  exact preserved

@[simp] theorem recordHeader_flatRecords
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordHeader (flatRecords input record) =
      toLex (Fin.cons (Routing.recordTag input record)
        (recordMetadata input record)) := by
  simp [recordHeader]

theorem recordHeader_complementRoutingTagsBits
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordHeader
        (flatRecords
          (complementRoutingTagsBits depth keyWidth
            (metadataWidth + valueWidth) input) record) =
      complementedRecordHeader (flatRecords input record) := by
  simp [recordHeader, complementedRecordHeader]

theorem recordHeader_predecessorCopyBits
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordHeader
        (flatRecords
          (predecessorCopyBits depth keyWidth metadataWidth valueWidth
            sourceTag destinationTag input) record) =
      recordHeader (flatRecords input record) := by
  simp [recordHeader]

@[simp] theorem complementedRecordHeader_predecessorCopyBits
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    complementedRecordHeader
        (flatRecords
          (predecessorCopyBits depth keyWidth metadataWidth valueWidth
            sourceTag destinationTag input) record) =
      complementedRecordHeader (flatRecords input record) := by
  simp [complementedRecordHeader]

/-- Semantic gather match followed by canonical metadata ordering. -/
def matchedCanonicalRoutingBits
    (depth keyWidth metadataWidth valueWidth : Nat)
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool :=
  canonicalSortBits depth keyWidth metadataWidth valueWidth
    (predecessorCopyBits depth keyWidth metadataWidth valueWidth false true
      (bitonicSortBits
        (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
        depth true input))

/-- Explicit two-sort gather circuit. -/
def matchedCanonicalRoutingCircuit
    (depth keyWidth metadataWidth valueWidth : Nat) :=
  (canonicalSortCircuit depth keyWidth metadataWidth valueWidth).comp
    (sortedPredecessorCopyCircuit depth keyWidth metadataWidth valueWidth
      false true)

/-- The exact gate count of `matchedCanonicalRoutingCircuit`. -/
@[simp] theorem matchedCanonicalRoutingCircuit_size
    (depth keyWidth metadataWidth valueWidth : Nat) :
    (matchedCanonicalRoutingCircuit depth keyWidth metadataWidth valueWidth).size =
      sortedPredecessorCopyGateCount depth keyWidth metadataWidth valueWidth false
          true +
        (canonicalSortCircuit depth keyWidth metadataWidth valueWidth).size := by
  simp [matchedCanonicalRoutingCircuit]

@[simp] theorem matchedCanonicalRoutingCircuit_eval
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    (matchedCanonicalRoutingCircuit depth keyWidth metadataWidth
      valueWidth).eval DeMorgan.interpretation input =
        matchedCanonicalRoutingBits depth keyWidth metadataWidth valueWidth
          input := by
  rw [matchedCanonicalRoutingCircuit, Circuit.eval_comp,
    canonicalSortCircuit_eval, sortedPredecessorCopyCircuit_eval]
  rfl

theorem matchedCanonicalRoutingCircuit_cost_le :
    (matchedCanonicalRoutingCircuit depth keyWidth metadataWidth
      valueWidth).cost DeMorgan.standardCost <=
      (depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth metadataWidth valueWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkBits depth (recordWidth keyWidth metadataWidth valueWidth) *
          (12 * keyWidth + 12)) +
      (networkBits depth (recordWidth keyWidth metadataWidth valueWidth) +
        depth * depth * networkRecords depth *
          ((2 * recordWidth keyWidth metadataWidth valueWidth) *
            (2 * ((metadataWidth + 1) *
              (6 * (metadataWidth + 1) + 4)) + 4))) := by
  rw [matchedCanonicalRoutingCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (sortedPredecessorCopyCircuit_cost_le false true)
    canonicalSortCircuit_cost_le

/-- The complete metadata-routing pipeline permutes complemented initial
`(tag, metadata)` headers. -/
theorem matchedCanonicalHeadersPermute
    (input : Fin (networkBits depth
      (recordWidth keyWidth metadataWidth valueWidth)) -> Bool) :
    let initiallySorted := bitonicSortBits
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
      depth true input
    let routed := predecessorCopyBits depth keyWidth metadataWidth valueWidth
      false true initiallySorted
    let output := canonicalSortBits depth keyWidth metadataWidth valueWidth
      routed
    Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords output record))
      (fun record => complementedRecordHeader (flatRecords input record)) := by
  dsimp only
  let initiallySorted := bitonicSortBits
    (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
    depth true input
  let routed := predecessorCopyBits depth keyWidth metadataWidth valueWidth
    false true initiallySorted
  let complemented := complementRoutingTagsBits depth keyWidth
    (metadataWidth + valueWidth) routed
  let output := canonicalSortBits depth keyWidth metadataWidth valueWidth
    routed
  have outputRecords : FlatRecordsPermute output complemented := by
    exact canonicalSortBits_recordsPermute routed
  have first : Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords output record))
      (fun record => recordHeader (flatRecords complemented record)) := by
    have mapped := Semantics.SequencePermutes.map recordHeader
      outputRecords
    simpa [Function.comp_def] using mapped
  have middle :
      (fun record => recordHeader (flatRecords complemented record)) =
        (fun record => complementedRecordHeader
          (flatRecords initiallySorted record)) := by
    funext record
    simp [complemented, routed, complementedRecordHeader]
  have initiallySortedRecords : FlatRecordsPermute initiallySorted input := by
    exact bitonicSortBits_recordsPermute
      (Routing.keyAndTagFitsRecord keyWidth (metadataWidth + valueWidth))
      depth true input
  have second : Semantics.SequencePermutes
      (fun record => complementedRecordHeader
        (flatRecords initiallySorted record))
      (fun record => complementedRecordHeader
        (flatRecords input record)) := by
    have mapped := Semantics.SequencePermutes.map
      complementedRecordHeader initiallySortedRecords
    simpa [Function.comp_def] using mapped
  rw [middle] at first
  exact first.trans second

/-! ## Canonical rank of destination metadata -/

/-- Destination metadata at one canonical prefix position. -/
noncomputable def destinationOrderMetadata
    (destinationFits : destinationCount <= 2 ^ orderWidth)
    (destination : Fin destinationCount) : Fin (orderWidth + 1) -> Bool :=
  activeRoutingKey
    (lexBitVectorAt (Fin.castLE destinationFits destination))

@[simp] theorem complementedRecordHeader_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (metadata : Fin metadataWidth -> Bool)
    (value : Fin valueWidth -> Bool) :
    complementedRecordHeader (packRecord key tag metadata value) =
      toLex (Fin.cons (!tag) metadata) := by
  simp [complementedRecordHeader]

theorem destinationHeader_injective : Function.Injective
    (CanonicalRouting.activeDestinationHeader
      (baseWidth := orderWidth)) := by
  intro left right equal
  unfold CanonicalRouting.activeDestinationHeader at equal
  rw [toLex_inj, Fin.cons_inj] at equal
  exact activeRoutingKey_injective equal.2

theorem complementedSourceHeader_not_lt_destination
    (key : Fin keyWidth -> Bool)
    (metadata : Fin (orderWidth + 1) -> Bool)
    (value : Fin valueWidth -> Bool)
    (target : Fin orderWidth -> Bool) :
    Not (complementedRecordHeader (packRecord key false metadata value) <
      CanonicalRouting.activeDestinationHeader target) := by
  simp only [complementedRecordHeader_packRecord]
  unfold CanonicalRouting.activeDestinationHeader
  change Not (Pi.Lex (fun a b : Fin (orderWidth + 2) => a < b)
    (fun a b : Bool => a < b)
    (Fin.cons true metadata)
    (Fin.cons false (activeRoutingKey target)))
  rw [Fin.pi_lex_lt_cons_cons]
  simp

theorem complementedPaddingHeader_not_lt_destination
    (key : Fin keyWidth -> Bool)
    (paddingTail : Fin orderWidth -> Bool)
    (value : Fin valueWidth -> Bool)
    (target : Fin orderWidth -> Bool) :
    Not (complementedRecordHeader
        (packRecord key true (paddingRoutingKey paddingTail) value) <
      CanonicalRouting.activeDestinationHeader target) := by
  simp only [complementedRecordHeader_packRecord, Bool.not_true]
  unfold CanonicalRouting.activeDestinationHeader paddingRoutingKey
    activeRoutingKey
  change Not (Pi.Lex (fun a b : Fin (orderWidth + 2) => a < b)
    (fun a b : Bool => a < b)
    (Fin.cons false (Fin.cons true paddingTail))
    (Fin.cons false (Fin.cons false target)))
  rw [Fin.pi_lex_lt_cons_cons, Fin.pi_lex_lt_cons_cons]
  simp

theorem complementedDestinationHeader_lt_iff
    (key : Fin keyWidth -> Bool)
    (left right : Fin orderWidth -> Bool)
    (value : Fin valueWidth -> Bool) :
    complementedRecordHeader
        (packRecord key true (activeRoutingKey left) value) <
        CanonicalRouting.activeDestinationHeader right ↔
      toLex left < toLex right := by
  simp only [complementedRecordHeader_packRecord, Bool.not_true]
  exact CanonicalRouting.activeDestinationHeader_lt_iff left right

/-- Exactly `target.val` initial records have complemented order metadata
strictly below the target destination's canonical metadata. -/
theorem routingRecordSequence_orderHeader_count_lt
    (destinationFits : destinationCount <= 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourceMetadata : Fin sourceCount -> Fin (orderWidth + 1) -> Bool)
    (sourceValues : Fin sourceCount -> Fin valueWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationValues : Fin destinationCount -> Fin valueWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin orderWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (target : Fin destinationCount) :
    (Semantics.matchingIndices
      (fun record => complementedRecordHeader
        (Routing.routingRecordSequence sourceKeys
          (fun source => Fin.append (sourceMetadata source)
            (sourceValues source))
          destinationKeys
          (fun destination => Fin.append
            (destinationOrderMetadata destinationFits destination)
            (destinationValues destination))
          paddingKeys
          (fun padding => Fin.append
            (paddingRoutingKey (paddingTails padding))
            (paddingValues padding)) record))
      (fun header => header < CanonicalRouting.activeDestinationHeader
        (lexBitVectorAt (Fin.castLE destinationFits target)))).card =
      target.val := by
  classical
  let targetBits := lexBitVectorAt (Fin.castLE destinationFits target)
  let targetHeader := CanonicalRouting.activeDestinationHeader targetBits
  let sourceRecords := fun source => packRecord (sourceKeys source) false
    (sourceMetadata source) (sourceValues source)
  let destinationRecords := fun destination =>
    packRecord (destinationKeys destination) true
      (destinationOrderMetadata destinationFits destination)
      (destinationValues destination)
  let paddingRecords := fun padding => packRecord (paddingKeys padding) true
    (paddingRoutingKey (paddingTails padding)) (paddingValues padding)
  have sourceCountZero :
      (Semantics.matchingIndices sourceRecords
        (fun record => complementedRecordHeader record < targetHeader)).card =
          0 := by
    unfold Semantics.matchingIndices
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro source _member
    exact complementedSourceHeader_not_lt_destination
      (sourceKeys source) (sourceMetadata source) (sourceValues source)
      targetBits
  have destinationFilter :
      Semantics.matchingIndices destinationRecords
          (fun record => complementedRecordHeader record < targetHeader) =
        Finset.Iio target := by
    ext destination
    simp only [Semantics.matchingIndices, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_Iio]
    change complementedRecordHeader
        (packRecord (destinationKeys destination) true
          (activeRoutingKey
            (lexBitVectorAt (Fin.castLE destinationFits destination)))
          (destinationValues destination)) <
        CanonicalRouting.activeDestinationHeader targetBits ↔
      destination < target
    rw [complementedDestinationHeader_lt_iff]
    unfold targetBits
    exact Iff.trans
      ((lexBitVectorAt_strictMono (width := orderWidth)).lt_iff_lt)
      (by rfl)
  have destinationCountValue :
      (Semantics.matchingIndices destinationRecords
        (fun record => complementedRecordHeader record < targetHeader)).card =
          target.val := by
    rw [destinationFilter]
    simp
  have paddingCountZero :
      (Semantics.matchingIndices paddingRecords
        (fun record => complementedRecordHeader record < targetHeader)).card =
          0 := by
    unfold Semantics.matchingIndices
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro padding _member
    exact complementedPaddingHeader_not_lt_destination
      (paddingKeys padding) (paddingTails padding) (paddingValues padding)
      targetBits
  unfold Routing.routingRecordSequence
  change
    (Semantics.matchingIndices
      (Fin.append (Fin.append sourceRecords destinationRecords)
        paddingRecords)
      (fun record => complementedRecordHeader record < targetHeader)).card =
        target.val
  rw [Semantics.matchingIndices_append_card,
    Semantics.matchingIndices_append_card, sourceCountZero,
    destinationCountValue, paddingCountZero]
  omega

/-- Flattening and exact-capacity casting preserve the destination metadata
rank count. -/
theorem routingInputBits_orderHeader_count_lt
    (destinationFits : destinationCount <= 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourceMetadata : Fin sourceCount -> Fin (orderWidth + 1) -> Bool)
    (sourceValues : Fin sourceCount -> Fin valueWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationValues : Fin destinationCount -> Fin valueWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin orderWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (target : Fin destinationCount) :
    let input := Routing.routingInputBits sourceKeys
      (fun source => Fin.append (sourceMetadata source) (sourceValues source))
      destinationKeys
      (fun destination => Fin.append
        (destinationOrderMetadata destinationFits destination)
        (destinationValues destination))
      paddingKeys
      (fun padding => Fin.append (paddingRoutingKey (paddingTails padding))
        (paddingValues padding)) recordCount
    (Semantics.matchingIndices
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun header => header < CanonicalRouting.activeDestinationHeader
        (lexBitVectorAt (Fin.castLE destinationFits target)))).card =
      target.val := by
  dsimp only
  rw [Routing.flatRecords_routingInputBits]
  unfold Routing.networkRoutingRecords
  exact (Semantics.matchingIndices_cast_card
    (fun record => complementedRecordHeader
      (Routing.routingRecordSequence sourceKeys
        (fun source => Fin.append (sourceMetadata source)
          (sourceValues source))
        destinationKeys
        (fun destination => Fin.append
          (destinationOrderMetadata destinationFits destination)
          (destinationValues destination))
        paddingKeys
        (fun padding => Fin.append
          (paddingRoutingKey (paddingTails padding))
          (paddingValues padding)) record))
    (fun header => header < CanonicalRouting.activeDestinationHeader
      (lexBitVectorAt (Fin.castLE destinationFits target)))
    recordCount).trans
    (routingRecordSequence_orderHeader_count_lt destinationFits sourceKeys
      sourceMetadata sourceValues destinationKeys destinationValues
      paddingKeys paddingTails paddingValues target)

/-! ## Unique canonical destination headers -/

theorem complementedRecordHeader_eq_activeDestinationHeader_iff
    (record : Fin (recordWidth keyWidth (orderWidth + 1) valueWidth) -> Bool)
    (target : Fin orderWidth -> Bool) :
    complementedRecordHeader record =
        CanonicalRouting.activeDestinationHeader target ↔
      Routing.packedRecordTag record = true /\
        packedRecordMetadata record = activeRoutingKey target := by
  unfold complementedRecordHeader CanonicalRouting.activeDestinationHeader
  rw [toLex_inj, Fin.cons_inj]
  simp

/-- The canonical metadata header for one destination occurs exactly once in
the semantic routing layout.  Matching keys need not be injective here: the
preserved destination-order metadata supplies the uniqueness. -/
theorem routingRecordSequence_unique_order_header
    (destinationFits : destinationCount <= 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourceMetadata : Fin sourceCount -> Fin (orderWidth + 1) -> Bool)
    (sourceValues : Fin sourceCount -> Fin valueWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationValues : Fin destinationCount -> Fin valueWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin orderWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (target : Fin destinationCount) :
    Sorting.Semantics.UniqueIndexWhere
      (Routing.routingRecordSequence sourceKeys
        (fun source => Fin.append (sourceMetadata source)
          (sourceValues source))
        destinationKeys
        (fun destination => Fin.append
          (destinationOrderMetadata destinationFits destination)
          (destinationValues destination))
        paddingKeys
        (fun padding => Fin.append
          (paddingRoutingKey (paddingTails padding))
          (paddingValues padding)))
      (fun record => complementedRecordHeader record =
        CanonicalRouting.activeDestinationHeader
          (lexBitVectorAt (Fin.castLE destinationFits target))) := by
  let targetBits := lexBitVectorAt (Fin.castLE destinationFits target)
  let predicate := fun record :
      Fin (recordWidth keyWidth (orderWidth + 1) valueWidth) -> Bool =>
    complementedRecordHeader record =
      CanonicalRouting.activeDestinationHeader targetBits
  let sourceRecords := fun source => packRecord (sourceKeys source) false
    (sourceMetadata source) (sourceValues source)
  let destinationRecords := fun destination =>
    packRecord (destinationKeys destination) true
      (destinationOrderMetadata destinationFits destination)
      (destinationValues destination)
  let paddingRecords := fun padding => packRecord (paddingKeys padding) true
    (paddingRoutingKey (paddingTails padding)) (paddingValues padding)
  have noSource : ∀ source, ¬ predicate (sourceRecords source) := by
    intro source sourceMatches
    have tagMatches :
        Routing.packedRecordTag (sourceRecords source) = true :=
      ((complementedRecordHeader_eq_activeDestinationHeader_iff
        (sourceRecords source) targetBits).mp sourceMatches).1
    simp [sourceRecords] at tagMatches
  have uniqueDestination :
      Sorting.Semantics.UniqueIndexWhere destinationRecords predicate := by
    unfold Sorting.Semantics.UniqueIndexWhere
    refine ⟨target, ?_, ?_⟩
    · refine (complementedRecordHeader_eq_activeDestinationHeader_iff
        (destinationRecords target) targetBits).mpr ?_
      exact ⟨by simp [destinationRecords], by
        simp [destinationRecords, destinationOrderMetadata, targetBits]⟩
    · intro other headerMatches
      have fields :
          Routing.packedRecordTag (destinationRecords other) = true /\
            packedRecordMetadata (destinationRecords other) =
              activeRoutingKey targetBits := by
        exact (complementedRecordHeader_eq_activeDestinationHeader_iff
          (destinationRecords other) targetBits).mp headerMatches
      have metadataEquality :
          activeRoutingKey
              (lexBitVectorAt (Fin.castLE destinationFits other)) =
            activeRoutingKey
              (lexBitVectorAt (Fin.castLE destinationFits target)) := by
        simpa [destinationRecords, destinationOrderMetadata, targetBits]
          using fields.2
      have bitsEquality := activeRoutingKey_injective metadataEquality
      have castEquality := lexBitVectorAt_injective bitsEquality
      apply Fin.ext
      simpa using congrArg Fin.val castEquality
  have noPadding : ∀ padding,
      ¬ predicate (paddingRecords padding) := by
    intro padding headerMatches
    have fields :
        Routing.packedRecordTag (paddingRecords padding) = true /\
          packedRecordMetadata (paddingRecords padding) =
            activeRoutingKey targetBits := by
      exact (complementedRecordHeader_eq_activeDestinationHeader_iff
        (paddingRecords padding) targetBits).mp headerMatches
    have metadataEquality :
        paddingRoutingKey (paddingTails padding) =
          activeRoutingKey targetBits := by
      simpa [paddingRecords] using fields.2
    exact paddingRoutingKey_ne_activeRoutingKey
      (paddingTails padding) targetBits metadataEquality
  unfold Routing.routingRecordSequence
  change Sorting.Semantics.UniqueIndexWhere
    (Fin.append (Fin.append sourceRecords destinationRecords)
      paddingRecords) predicate
  exact (Sorting.Semantics.UniqueIndexWhere.append_right noSource
    uniqueDestination).append_left noPadding

/-- Exact-capacity casting and flattening retain the unique canonical
destination metadata header. -/
theorem routingInputBits_unique_order_header
    (destinationFits : destinationCount <= 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourceMetadata : Fin sourceCount -> Fin (orderWidth + 1) -> Bool)
    (sourceValues : Fin sourceCount -> Fin valueWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationValues : Fin destinationCount -> Fin valueWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin orderWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (target : Fin destinationCount) :
    let input := Routing.routingInputBits sourceKeys
      (fun source => Fin.append (sourceMetadata source) (sourceValues source))
      destinationKeys
      (fun destination => Fin.append
        (destinationOrderMetadata destinationFits destination)
        (destinationValues destination))
      paddingKeys
      (fun padding => Fin.append (paddingRoutingKey (paddingTails padding))
        (paddingValues padding)) recordCount
    Sorting.Semantics.UniqueIndexWhere (flatRecords input)
      (fun record => complementedRecordHeader record =
        CanonicalRouting.activeDestinationHeader
          (lexBitVectorAt (Fin.castLE destinationFits target))) := by
  dsimp only
  rw [Routing.flatRecords_routingInputBits]
  exact (routingRecordSequence_unique_order_header destinationFits sourceKeys
    sourceMetadata sourceValues destinationKeys destinationValues paddingKeys
    paddingTails paddingValues target).cast recordCount

/-! ## Fixed output positions -/

/-- After matching by the runtime key and sorting by preserved destination
metadata, destination `target` occupies literal output record `target`. -/
theorem matchedCanonicalRoutingBits_fixed_header
    (destinationFits : destinationCount <= 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourceMetadata : Fin sourceCount -> Fin (orderWidth + 1) -> Bool)
    (sourceValues : Fin sourceCount -> Fin valueWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationValues : Fin destinationCount -> Fin valueWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin orderWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (target : Fin destinationCount) :
    let input := Routing.routingInputBits sourceKeys
      (fun source => Fin.append (sourceMetadata source) (sourceValues source))
      destinationKeys
      (fun destination => Fin.append
        (destinationOrderMetadata destinationFits destination)
        (destinationValues destination))
      paddingKeys
      (fun padding => Fin.append (paddingRoutingKey (paddingTails padding))
        (paddingValues padding)) recordCount
    let output := matchedCanonicalRoutingBits depth keyWidth
      (orderWidth + 1) valueWidth input
    let destinationFitsNetwork : destinationCount <= networkRecords depth := by
      omega
    recordHeader
        (flatRecords output (Fin.castLE destinationFitsNetwork target)) =
      CanonicalRouting.activeDestinationHeader
        (lexBitVectorAt (Fin.castLE destinationFits target)) := by
  dsimp only
  let input := Routing.routingInputBits sourceKeys
    (fun source => Fin.append (sourceMetadata source) (sourceValues source))
    destinationKeys
    (fun destination => Fin.append
      (destinationOrderMetadata destinationFits destination)
      (destinationValues destination))
    paddingKeys
    (fun padding => Fin.append (paddingRoutingKey (paddingTails padding))
      (paddingValues padding)) recordCount
  let output := matchedCanonicalRoutingBits depth keyWidth
    (orderWidth + 1) valueWidth input
  let targetHeader := CanonicalRouting.activeDestinationHeader
    (lexBitVectorAt (Fin.castLE destinationFits target))
  have uniqueInitialHeader : Sorting.Semantics.UniqueIndexWhere
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun header => header = targetHeader) := by
    exact routingInputBits_unique_order_header destinationFits sourceKeys
      sourceMetadata sourceValues destinationKeys destinationValues paddingKeys
      paddingTails paddingValues recordCount target
  have headersPermute : Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords output record))
      (fun record => complementedRecordHeader (flatRecords input record)) := by
    exact matchedCanonicalHeadersPermute input
  have uniqueOutputHeader :=
    Sorting.Semantics.UniqueIndexWhere.of_sequencePermutes
    headersPermute uniqueInitialHeader
  obtain ⟨outputIndex, outputMatches, outputOnly⟩ := uniqueOutputHeader
  have outputIncreasing : Semantics.SequenceIncreasing
      (fun record => recordHeader (flatRecords output record)) := by
    have sorted := canonicalSortBits_keysSorted
      (predecessorCopyBits depth keyWidth (orderWidth + 1) valueWidth
        false true
        (bitonicSortBits
          (Routing.keyAndTagFitsRecord keyWidth
            ((orderWidth + 1) + valueWidth)) depth true input))
    unfold FlatKeysSortedBy FlatKeysSorted Semantics.SequenceSorted at sorted
    simp only [ite_true] at sorted
    intro left right before
    have ordered := sorted left right before
    change
      flatRecordKey
          (metadataOrderKeyFits keyWidth (orderWidth + 1) valueWidth)
          (flatRecords
            (reindexRecordBits
              (metadataOrderBitOrder keyWidth (orderWidth + 1) valueWidth)
              output) left) <=
        flatRecordKey
          (metadataOrderKeyFits keyWidth (orderWidth + 1) valueWidth)
          (flatRecords
            (reindexRecordBits
              (metadataOrderBitOrder keyWidth (orderWidth + 1) valueWidth)
              output) right)
        at ordered
    rw [metadataOrderVirtualKey output left,
      metadataOrderVirtualKey output right] at ordered
    simpa only [recordHeader_flatRecords] using ordered
  have outputRank :
      (Semantics.matchingIndices
        (fun record => recordHeader (flatRecords output record))
        (fun header => header < targetHeader)).card = outputIndex.val := by
    rw [← outputMatches]
    apply Semantics.matchingIndices_lt_card_eq_index
      (fun record => recordHeader (flatRecords output record))
      outputIncreasing outputIndex
    intro other equalHeader
    apply outputOnly other
    exact equalHeader.trans outputMatches
  have initialRank :
      (Semantics.matchingIndices
        (fun record => complementedRecordHeader (flatRecords input record))
        (fun header => header < targetHeader)).card = target.val := by
    exact routingInputBits_orderHeader_count_lt destinationFits sourceKeys
      sourceMetadata sourceValues destinationKeys destinationValues paddingKeys
      paddingTails paddingValues recordCount target
  have rankPreserved := headersPermute.matchingIndices_card_eq
    (fun header => header < targetHeader)
  have outputIndexValue : outputIndex.val = target.val := by
    exact outputRank.symm.trans (rankPreserved.trans initialRank)
  have destinationFitsNetwork :
      destinationCount <= networkRecords depth := by
    omega
  have outputIndexEquality :
      outputIndex = Fin.castLE destinationFitsNetwork target := by
    apply Fin.ext
    exact outputIndexValue
  rw [← outputIndexEquality]
  exact outputMatches

/-- The value copied into destination `target` also occupies its literal
canonical output record.  This is the generic fixed-wire correctness theorem
used by the gather pass. -/
theorem matchedCanonicalRoutingBits_fixed_value
    (destinationFits : destinationCount <= 2 ^ orderWidth)
    (sourceKeys : Fin sourceCount -> Fin keyWidth -> Bool)
    (sourceMetadata : Fin sourceCount -> Fin (orderWidth + 1) -> Bool)
    (sourceValues : Fin sourceCount -> Fin valueWidth -> Bool)
    (destinationKeys : Fin destinationCount -> Fin keyWidth -> Bool)
    (destinationValues : Fin destinationCount -> Fin valueWidth -> Bool)
    (paddingKeys : Fin paddingCount -> Fin keyWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin orderWidth -> Bool)
    (paddingValues : Fin paddingCount -> Fin valueWidth -> Bool)
    (sourceKeysInjective : Function.Injective sourceKeys)
    (destinationKeysInjective : Function.Injective destinationKeys)
    (sourceFor : Fin destinationCount -> Fin sourceCount)
    (matchingKey : forall destination,
      sourceKeys (sourceFor destination) = destinationKeys destination)
    (paddingAvoids : forall padding destination,
      paddingKeys padding ≠ destinationKeys destination)
    (recordCount : sourceCount + destinationCount + paddingCount =
      networkRecords depth)
    (target : Fin destinationCount) :
    let input := Routing.routingInputBits sourceKeys
      (fun source => Fin.append (sourceMetadata source) (sourceValues source))
      destinationKeys
      (fun destination => Fin.append
        (destinationOrderMetadata destinationFits destination)
        (destinationValues destination))
      paddingKeys
      (fun padding => Fin.append (paddingRoutingKey (paddingTails padding))
        (paddingValues padding)) recordCount
    let output := matchedCanonicalRoutingBits depth keyWidth
      (orderWidth + 1) valueWidth input
    let destinationFitsNetwork : destinationCount <= networkRecords depth := by
      omega
    recordValue output (Fin.castLE destinationFitsNetwork target) =
      sourceValues (sourceFor target) := by
  dsimp only
  let sourcePayloads := fun source =>
    Fin.append (sourceMetadata source) (sourceValues source)
  let destinationPayloads := fun destination =>
    Fin.append (destinationOrderMetadata destinationFits destination)
      (destinationValues destination)
  let paddingPayloads := fun padding =>
    Fin.append (paddingRoutingKey (paddingTails padding))
      (paddingValues padding)
  let input := Routing.routingInputBits sourceKeys sourcePayloads
    destinationKeys destinationPayloads paddingKeys paddingPayloads
    recordCount
  let initiallySorted := bitonicSortBits
    (Routing.keyAndTagFitsRecord keyWidth
      ((orderWidth + 1) + valueWidth)) depth true input
  let routed := predecessorCopyBits depth keyWidth (orderWidth + 1)
    valueWidth false true initiallySorted
  let complemented := complementRoutingTagsBits depth keyWidth
    ((orderWidth + 1) + valueWidth) routed
  let output := matchedCanonicalRoutingBits depth keyWidth
    (orderWidth + 1) valueWidth input
  let targetHeader := CanonicalRouting.activeDestinationHeader
    (lexBitVectorAt (Fin.castLE destinationFits target))
  have destinationFitsNetwork : destinationCount <= networkRecords depth := by
    omega
  let fixedIndex : Fin (networkRecords depth) :=
    Fin.castLE destinationFitsNetwork target
  have fixedHeader :
      recordHeader (flatRecords output fixedIndex) = targetHeader := by
    exact matchedCanonicalRoutingBits_fixed_header destinationFits sourceKeys
      sourceMetadata sourceValues destinationKeys destinationValues paddingKeys
      paddingTails paddingValues recordCount target
  have initiallySortedPermutes : FlatRecordsPermute initiallySorted input := by
    exact bitonicSortBits_recordsPermute
      (Routing.keyAndTagFitsRecord keyWidth
        ((orderWidth + 1) + valueWidth)) depth true input
  have uniqueInitialHeader : Sorting.Semantics.UniqueIndexWhere
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun header => header = targetHeader) := by
    exact routingInputBits_unique_order_header destinationFits sourceKeys
      sourceMetadata sourceValues destinationKeys destinationValues paddingKeys
      paddingTails paddingValues recordCount target
  have uniqueSortedHeader :=
    Sorting.Semantics.UniqueIndexWhere.of_sequencePermutes
    (Semantics.SequencePermutes.map complementedRecordHeader
      initiallySortedPermutes)
    uniqueInitialHeader
  obtain ⟨headerIndex, headerIndexMatches, headerIndexOnly⟩ :=
    uniqueSortedHeader
  have uniqueSourceRaw := Routing.routingInputBits_unique_source sourceKeys
    sourcePayloads destinationKeys destinationPayloads paddingKeys
    paddingPayloads sourceKeysInjective recordCount (sourceFor target)
  have uniqueSource : Sorting.Semantics.UniqueIndexWhere (flatRecords input)
      (Routing.recordHasKeyTag (destinationKeys target) false) := by
    simpa only [matchingKey target] using uniqueSourceRaw
  have uniqueDestination := Routing.routingInputBits_unique_destination
    sourceKeys sourcePayloads destinationKeys destinationPayloads paddingKeys
    paddingPayloads destinationKeysInjective paddingAvoids recordCount target
  obtain ⟨sourceInput, _sourceSorted, destinationSorted,
      sourceInputMatches, _sourceSortedMatches, destinationSortedMatches,
      routedValue⟩ :=
    sortedPredecessorCopyCircuit_routes_unique_key input
      (destinationKeys target) uniqueSource uniqueDestination
  rw [sortedPredecessorCopyCircuit_eval] at routedValue
  change recordValue routed destinationSorted =
    packedRecordValue (flatRecords input sourceInput) at routedValue
  let expectedSource := Routing.networkRoutingSourceIndex recordCount
    (sourceFor target)
  have expectedSourceRecord :
      flatRecords input expectedSource =
        packRecord (sourceKeys (sourceFor target)) false
          (sourceMetadata (sourceFor target))
          (sourceValues (sourceFor target)) := by
    change flatRecords input expectedSource =
      Routing.packRecord (sourceKeys (sourceFor target)) false
        (sourcePayloads (sourceFor target))
    simp only [input, Routing.flatRecords_routingInputBits]
    exact Routing.networkRoutingRecords_source sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      recordCount (sourceFor target)
  have expectedSourceMatches : Routing.recordHasKeyTag
      (destinationKeys target) false
      (flatRecords input expectedSource) := by
    rw [expectedSourceRecord]
    simp [Routing.recordHasKeyTag, matchingKey target]
  obtain ⟨uniqueSourceIndex, _uniqueSourceMatches, uniqueSourceOnly⟩ :=
    uniqueSource
  have sourceInputIndex := uniqueSourceOnly sourceInput sourceInputMatches
  have expectedSourceIndex := uniqueSourceOnly expectedSource
    expectedSourceMatches
  have sourceInputEquality : sourceInput = expectedSource :=
    sourceInputIndex.trans expectedSourceIndex.symm
  have sourceInputValue :
      packedRecordValue (flatRecords input sourceInput) =
        sourceValues (sourceFor target) := by
    rw [sourceInputEquality, expectedSourceRecord]
    simp
  let expectedDestination := Routing.networkRoutingDestinationIndex
    recordCount target
  have expectedDestinationRecord :
      flatRecords input expectedDestination =
        packRecord (destinationKeys target) true
          (destinationOrderMetadata destinationFits target)
          (destinationValues target) := by
    change flatRecords input expectedDestination =
      Routing.packRecord (destinationKeys target) true
        (destinationPayloads target)
    simp only [input, Routing.flatRecords_routingInputBits]
    exact Routing.networkRoutingRecords_destination sourceKeys sourcePayloads
      destinationKeys destinationPayloads paddingKeys paddingPayloads
      recordCount target
  have expectedDestinationMatches : Routing.recordHasKeyTag
      (destinationKeys target) true
      (flatRecords input expectedDestination) := by
    rw [expectedDestinationRecord]
    simp [Routing.recordHasKeyTag]
  obtain ⟨uniqueDestinationIndex, _uniqueDestinationMatches,
      uniqueDestinationOnly⟩ := uniqueDestination
  obtain ⟨correspondingInput, sortedRecordEquality⟩ :=
    Sorting.FlatRecordsPermute.rangeContained initiallySortedPermutes
      destinationSorted
  have correspondingDestinationMatches : Routing.recordHasKeyTag
      (destinationKeys target) true
      (flatRecords input correspondingInput) := by
    rw [← sortedRecordEquality]
    exact destinationSortedMatches
  have correspondingInputIndex := uniqueDestinationOnly correspondingInput
    correspondingDestinationMatches
  have expectedDestinationIndex := uniqueDestinationOnly expectedDestination
    expectedDestinationMatches
  have correspondingInputEquality : correspondingInput =
      expectedDestination :=
    correspondingInputIndex.trans expectedDestinationIndex.symm
  have destinationSortedHeader :
      complementedRecordHeader
          (flatRecords initiallySorted destinationSorted) = targetHeader := by
    rw [sortedRecordEquality, correspondingInputEquality,
      expectedDestinationRecord]
    simp [targetHeader, destinationOrderMetadata,
      CanonicalRouting.activeDestinationHeader]
  have destinationSortedEquality : destinationSorted = headerIndex :=
    headerIndexOnly destinationSorted destinationSortedHeader
  have canonicalRecords : FlatRecordsPermute output complemented := by
    change FlatRecordsPermute
      (canonicalSortBits depth keyWidth (orderWidth + 1) valueWidth routed)
      complemented
    exact canonicalSortBits_recordsPermute routed
  obtain ⟨preCanonicalIndex, canonicalRecordEquality⟩ :=
    Sorting.FlatRecordsPermute.rangeContained canonicalRecords fixedIndex
  have preCanonicalHeader :
      recordHeader (flatRecords complemented preCanonicalIndex) =
        targetHeader := by
    rw [← canonicalRecordEquality]
    exact fixedHeader
  have preCanonicalRoutedHeader :
      complementedRecordHeader (flatRecords routed preCanonicalIndex) =
        targetHeader := by
    rw [← recordHeader_complementRoutingTagsBits routed preCanonicalIndex]
    exact preCanonicalHeader
  have preCanonicalSortedHeader :
      complementedRecordHeader
          (flatRecords initiallySorted preCanonicalIndex) = targetHeader := by
    rw [← complementedRecordHeader_predecessorCopyBits false true
      initiallySorted preCanonicalIndex]
    exact preCanonicalRoutedHeader
  have preCanonicalIndexEquality : preCanonicalIndex = destinationSorted := by
    calc
      preCanonicalIndex = headerIndex :=
        headerIndexOnly preCanonicalIndex preCanonicalSortedHeader
      _ = destinationSorted := destinationSortedEquality.symm
  have valueMoved := congrArg packedRecordValue canonicalRecordEquality
  simp only [packedRecordValue_flatRecords] at valueMoved
  calc
    recordValue output fixedIndex =
        recordValue complemented preCanonicalIndex := valueMoved
    _ = recordValue routed preCanonicalIndex :=
      recordValue_complementRoutingTagsBits routed preCanonicalIndex
    _ = recordValue routed destinationSorted := by
      rw [preCanonicalIndexEquality]
    _ = packedRecordValue (flatRecords input sourceInput) := routedValue
    _ = sourceValues (sourceFor target) := sourceInputValue

end CanonicalMetadataRouting
end MassProduction
end Algebraic
