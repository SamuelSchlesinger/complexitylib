/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.IncidenceRouting
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Canonical fixed-wire routing layouts

The matching pass identifies a destination by data-dependent sorted position.
Resource circuits, however, need one fixed wire for every `(group, point)`
slot.  This module adds the second routing sort used in the manuscript:

1. complement every source/destination tag after predecessor copying;
2. reinterpret a record's prefix as `(tag, key)` rather than `(key, tag)`;
3. sort again in ascending order.

For a full active-key-space destination array, active destinations then form
the initial block, in canonical lexicographic key order.  All transformations
are explicit De Morgan circuits or free wire permutations.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace CanonicalRouting

open scoped BigOperators
open Sorting

/-! ## Complementing the physical tag field -/

/-- One output formula for the tag-complement pass. -/
def complementTagOutputExpression
    (depth keyWidth payloadWidth : Nat)
    (output : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth))) :
    DeMorgan.Expression (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) :=
  let recordAndBit :=
    (finProdFinEquiv
      (m := networkRecords depth)
      (n := Routing.recordWidth keyWidth payloadWidth)).symm output
  if recordAndBit.2 = Routing.tagBit keyWidth payloadWidth then
    .not (.input output)
  else
    .input output

/-- Semantic tag complement on a packed routing array. -/
def complementRoutingTagsBits
    (depth keyWidth payloadWidth : Nat)
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool :=
  fun output =>
    (complementTagOutputExpression depth keyWidth payloadWidth output).eval
      input

/-- Gate count of one tag-complement output formula. -/
@[reducible] def complementTagOutputGateCount
    (depth keyWidth payloadWidth : Nat)
    (output : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth))) : Nat :=
  (complementTagOutputExpression depth keyWidth payloadWidth output).gateCount

/-- Explicit circuit complementing precisely the tag bit of every record. -/
def complementRoutingTagsCircuit
    (depth keyWidth payloadWidth : Nat) :
    Circuit DeMorgan.signature
      (networkBits depth (Routing.recordWidth keyWidth payloadWidth))
      (∑ output, complementTagOutputGateCount depth keyWidth payloadWidth
        output)
      (networkBits depth (Routing.recordWidth keyWidth payloadWidth)) :=
  Circuit.parallelFin
    (networkBits depth (Routing.recordWidth keyWidth payloadWidth))
    (complementTagOutputGateCount depth keyWidth payloadWidth) fun output =>
      (complementTagOutputExpression depth keyWidth payloadWidth output).circuit

@[simp] theorem complementRoutingTagsCircuit_eval
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    (complementRoutingTagsCircuit depth keyWidth payloadWidth).eval
        DeMorgan.interpretation input =
      complementRoutingTagsBits depth keyWidth payloadWidth input := by
  funext output
  rw [complementRoutingTagsCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  rfl

@[simp] theorem complementRoutingTagsBits_recordKey
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    Routing.recordKey
        (complementRoutingTagsBits depth keyWidth payloadWidth input) record =
      Routing.recordKey input record := by
  funext bit
  unfold Routing.recordKey complementRoutingTagsBits
  unfold complementTagOutputExpression
  simp only [Routing.finProdFinEquiv_symm_recordBitIndex]
  have different :
      Routing.keyBit keyWidth payloadWidth bit ≠
        Routing.tagBit keyWidth payloadWidth := by
    intro equal
    have values := congrArg Fin.val equal
    change bit.val = keyWidth at values
    exact (Nat.ne_of_lt bit.isLt) values
  rw [ite_eq_right different]
  rfl

@[simp] theorem complementRoutingTagsBits_recordTag
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    Routing.recordTag
        (complementRoutingTagsBits depth keyWidth payloadWidth input) record =
      !(Routing.recordTag input record) := by
  unfold Routing.recordTag complementRoutingTagsBits
  unfold complementTagOutputExpression
  simp only [Routing.finProdFinEquiv_symm_recordBitIndex]
  simp only [ite_eq_left, DeMorgan.Expression.eval]

@[simp] theorem complementRoutingTagsBits_recordPayload
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    Routing.recordPayload
        (complementRoutingTagsBits depth keyWidth payloadWidth input) record =
      Routing.recordPayload input record := by
  funext bit
  unfold Routing.recordPayload complementRoutingTagsBits
  unfold complementTagOutputExpression
  simp only [Routing.finProdFinEquiv_symm_recordBitIndex]
  have different :
      Routing.payloadBit keyWidth payloadWidth bit ≠
        Routing.tagBit keyWidth payloadWidth := by
    intro equal
    have values := congrArg Fin.val equal
    change keyWidth + 1 + bit.val = keyWidth at values
    omega
  rw [ite_eq_right different]
  rfl

theorem complementTagOutputExpression_standardCost_le
    (output : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth))) :
    (complementTagOutputExpression depth keyWidth payloadWidth output).standardCost
      <= 1 := by
  unfold complementTagOutputExpression
  dsimp only
  split_ifs <;> simp [DeMorgan.Expression.standardCost]

/-- The tag complement costs at most one gate per physical input bit (and in
fact exactly one gate per record). -/
theorem complementRoutingTagsCircuit_cost_le :
    (complementRoutingTagsCircuit depth keyWidth payloadWidth).cost
        DeMorgan.standardCost <=
      networkBits depth (Routing.recordWidth keyWidth payloadWidth) := by
  rw [complementRoutingTagsCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    (∑ output,
      (complementTagOutputExpression depth keyWidth payloadWidth output).standardCost)
        <= ∑ _output : Fin (networkBits depth
          (Routing.recordWidth keyWidth payloadWidth)), 1 := by
      exact Finset.sum_le_sum fun output _ =>
        complementTagOutputExpression_standardCost_le output
    _ = networkBits depth (Routing.recordWidth keyWidth payloadWidth) := by
      simp

/-! ## Sorting by `(tag, key)` -/

/-- Within-record permutation taking the virtual order `(tag, key, payload)`
to the physical order `(key, tag, payload)`. -/
def tagFirstBitOrder (keyWidth payloadWidth : Nat) :
    Equiv.Perm (Fin (Routing.recordWidth keyWidth payloadWidth)) :=
  finSumFinEquiv.symm |>.trans
    (((finRotate (keyWidth + 1)).symm).sumCongr (Equiv.refl _)) |>.trans
      finSumFinEquiv

/-- The selected virtual prefix is exactly the physical tag followed by the
physical routing key. -/
theorem tagFirstVirtualKey
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    flatRecordKey (keyWidth := keyWidth + 1)
        (Routing.keyAndTagFitsRecord keyWidth payloadWidth)
        (flatRecords
          (reindexRecordBits (tagFirstBitOrder keyWidth payloadWidth) input)
          record) =
      toLex (Fin.cons (Routing.recordTag input record)
        (Routing.recordKey input record)) := by
  unfold flatRecordKey
  rw [toLex_inj]
  funext bit
  rw [flatRecords_reindexRecordBits]
  change
    flatRecords input record
        (tagFirstBitOrder keyWidth payloadWidth
          (Fin.castLE (Routing.keyAndTagFitsRecord keyWidth payloadWidth)
            bit)) =
      (@Fin.cons keyWidth (fun _ => Bool)
        (Routing.recordTag input record)
        (Routing.recordKey input record)) bit
  let physicalPrefix : Fin (keyWidth + 1) -> Bool :=
    Fin.snoc (Routing.recordKey input record) (Routing.recordTag input record)
  have physicalPrefix_eq :
      forall prefixBit,
        flatRecords input record (Fin.castAdd payloadWidth prefixBit) =
          physicalPrefix prefixBit := by
    intro prefixBit
    refine Fin.lastCases ?_ (fun keyBit => ?_) prefixBit
    · simp only [physicalPrefix, Fin.snoc_last]
      unfold Routing.recordTag flatRecords networkRecord
      apply congrArg input
      apply Fin.ext
      rfl
    · simp only [physicalPrefix, Fin.snoc_castSucc]
      unfold Routing.recordKey flatRecords networkRecord
      apply congrArg input
      apply Fin.ext
      rfl
  have orderPrefix :
      tagFirstBitOrder keyWidth payloadWidth
        (Fin.castAdd payloadWidth bit) =
        Fin.castAdd payloadWidth ((finRotate (keyWidth + 1)).symm bit) := by
    unfold tagFirstBitOrder Routing.recordWidth
    rw [Equiv.trans_apply, Equiv.trans_apply]
    rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply]
    change finSumFinEquiv
        (Sum.inl ((finRotate (keyWidth + 1)).symm bit)) = _
    exact finSumFinEquiv_apply_left _
  rw [show Fin.castLE (Routing.keyAndTagFitsRecord keyWidth payloadWidth) bit =
      Fin.castAdd payloadWidth bit by
    apply Fin.ext
    rfl]
  rw [orderPrefix, physicalPrefix_eq]
  have rotated := congrFun
    (Fin.snoc_eq_cons_rotate (Routing.recordKey input record)
      (Routing.recordTag input record))
    ((finRotate (keyWidth + 1)).symm bit)
  simpa [physicalPrefix] using rotated

/-- The complete canonicalization pass: flip tags, then sort by `(tag, key)`.
The matching/copy pass is supplied separately so this primitive is reusable
for both scatter and gather. -/
def canonicalSortBits
    (depth keyWidth payloadWidth : Nat)
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool :=
  bitonicSortByBits (tagFirstBitOrder keyWidth payloadWidth)
    (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true
    (complementRoutingTagsBits depth keyWidth payloadWidth input)

/-- Explicit tag-flip and canonical-sort circuit. -/
def canonicalSortCircuit
    (depth keyWidth payloadWidth : Nat) :=
  (bitonicSortByCircuit (tagFirstBitOrder keyWidth payloadWidth)
      (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true).comp
    (complementRoutingTagsCircuit depth keyWidth payloadWidth)

@[simp] theorem canonicalSortCircuit_eval
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    (canonicalSortCircuit depth keyWidth payloadWidth).eval
        DeMorgan.interpretation input =
      canonicalSortBits depth keyWidth payloadWidth input := by
  rw [canonicalSortCircuit, Circuit.eval_comp,
    bitonicSortByCircuit_eval, complementRoutingTagsCircuit_eval]
  rfl

theorem canonicalSortBits_recordsPermute
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    FlatRecordsPermute
      (canonicalSortBits depth keyWidth payloadWidth input)
      (complementRoutingTagsBits depth keyWidth payloadWidth input) := by
  exact bitonicSortByBits_recordsPermute
    (tagFirstBitOrder keyWidth payloadWidth)
    (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true _

theorem canonicalSortBits_keysSorted
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    FlatKeysSortedBy (tagFirstBitOrder keyWidth payloadWidth)
      (Routing.keyAndTagFitsRecord keyWidth payloadWidth) true
      (canonicalSortBits depth keyWidth payloadWidth input) := by
  exact bitonicSortByBits_keysSorted
    (tagFirstBitOrder keyWidth payloadWidth)
    (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true _

theorem canonicalSortCircuit_cost_le :
    (canonicalSortCircuit depth keyWidth payloadWidth).cost
        DeMorgan.standardCost <=
      networkBits depth (Routing.recordWidth keyWidth payloadWidth) +
        depth * depth * networkRecords depth *
          ((2 * Routing.recordWidth keyWidth payloadWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) := by
  rw [canonicalSortCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    complementRoutingTagsCircuit_cost_le
    (bitonicSortByCircuit_cost_le
      (tagFirstBitOrder keyWidth payloadWidth)
      (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true)

/-! ## Header permutations through the two routing sorts -/

/-- Canonical header of a standalone physical routing record. -/
def recordHeader
    (record : Fin (Routing.recordWidth keyWidth payloadWidth) -> Bool) :
    Lex (Fin (keyWidth + 1) -> Bool) :=
  toLex (Fin.cons (Routing.packedRecordTag record)
    (Routing.packedRecordKey record))

/-- Header obtained after complementing the tag of a standalone record. -/
def complementedRecordHeader
    (record : Fin (Routing.recordWidth keyWidth payloadWidth) -> Bool) :
    Lex (Fin (keyWidth + 1) -> Bool) :=
  toLex (Fin.cons (!(Routing.packedRecordTag record))
    (Routing.packedRecordKey record))

/-- Canonical header occupied by the active destination for one unmarked
base key. -/
def activeDestinationHeader
    (baseKey : Fin baseWidth -> Bool) :
    Lex (Fin (baseWidth + 2) -> Bool) :=
  toLex (Fin.cons false (activeRoutingKey baseKey))

@[simp] theorem complementedRecordHeader_packRecord
    (key : Fin keyWidth -> Bool)
    (tag : Bool)
    (payload : Fin payloadWidth -> Bool) :
    complementedRecordHeader (Routing.packRecord key tag payload) =
      toLex (Fin.cons (!tag) key) := by
  simp [complementedRecordHeader]

theorem activeDestinationHeader_lt_iff
    (left right : Fin baseWidth -> Bool) :
    activeDestinationHeader left < activeDestinationHeader right ↔
      toLex left < toLex right := by
  unfold activeDestinationHeader activeRoutingKey
  change Pi.Lex (fun a b : Fin (baseWidth + 2) => a < b)
      (fun a b : Bool => a < b)
      (Fin.cons false (Fin.cons false left))
      (Fin.cons false (Fin.cons false right)) ↔
    Pi.Lex (fun a b : Fin baseWidth => a < b)
      (fun a b : Bool => a < b) left right
  rw [Fin.pi_lex_lt_cons_cons, Fin.pi_lex_lt_cons_cons]
  simp

theorem complementedSourceHeader_not_lt_active
    (sourceKey : Fin (baseWidth + 1) -> Bool)
    (sourcePayload : Fin payloadWidth -> Bool)
    (target : Fin baseWidth -> Bool) :
    Not (complementedRecordHeader
        (Routing.packRecord sourceKey false sourcePayload) <
      activeDestinationHeader target) := by
  simp only [complementedRecordHeader_packRecord]
  unfold activeDestinationHeader
  change Not (Pi.Lex (fun a b : Fin (baseWidth + 2) => a < b)
    (fun a b : Bool => a < b)
    (Fin.cons true sourceKey)
    (Fin.cons false (activeRoutingKey target)))
  rw [Fin.pi_lex_lt_cons_cons]
  simp

theorem complementedPaddingHeader_not_lt_active
    (paddingTail : Fin baseWidth -> Bool)
    (paddingPayload : Fin payloadWidth -> Bool)
    (target : Fin baseWidth -> Bool) :
    Not (complementedRecordHeader
        (Routing.packRecord (paddingRoutingKey paddingTail) true
          paddingPayload) <
      activeDestinationHeader target) := by
  simp only [complementedRecordHeader_packRecord]
  unfold activeDestinationHeader paddingRoutingKey activeRoutingKey
  change Not (Pi.Lex (fun a b : Fin (baseWidth + 2) => a < b)
    (fun a b : Bool => a < b)
    (Fin.cons false (Fin.cons true paddingTail))
    (Fin.cons false (Fin.cons false target)))
  rw [Fin.pi_lex_lt_cons_cons, Fin.pi_lex_lt_cons_cons]
  simp

theorem complementedActiveDestinationHeader_lt_iff
    (left right : Fin baseWidth -> Bool)
    (payload : Fin payloadWidth -> Bool) :
    complementedRecordHeader
        (Routing.packRecord (activeRoutingKey left) true payload) <
        activeDestinationHeader right ↔
      toLex left < toLex right := by
  simp only [complementedRecordHeader_packRecord, Bool.not_true]
  exact activeDestinationHeader_lt_iff left right

@[simp] theorem recordHeader_flatRecords
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordHeader (flatRecords input record) =
      toLex (Fin.cons (Routing.recordTag input record)
        (Routing.recordKey input record)) := by
  simp [recordHeader]

theorem recordHeader_complementRoutingTagsBits
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordHeader
        (flatRecords
          (complementRoutingTagsBits depth keyWidth payloadWidth input)
          record) =
      complementedRecordHeader (flatRecords input record) := by
  simp [recordHeader, complementedRecordHeader]

theorem recordHeader_predecessorCopyBits
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth)) :
    recordHeader
        (flatRecords
          (Routing.predecessorCopyBits depth keyWidth payloadWidth
            sourceTag destinationTag input) record) =
      recordHeader (flatRecords input record) := by
  simp [recordHeader]

/-- Canonical-routing compatibility theorem for preservation of matching
position counts under a sequence permutation. -/
theorem matchingIndices_card_eq_of_sequencePermutes
    {output input : Fin n -> α}
    (predicate : α -> Prop)
    (permuted : Semantics.SequencePermutes output input) :
    (Semantics.matchingIndices output predicate).card =
      (Semantics.matchingIndices input predicate).card :=
  permuted.matchingIndices_card_eq predicate

/-- Canonical-routing compatibility theorem for matching-position counts in
an appended sequence. -/
theorem matchingIndices_append_card
    {α : Type*}
    (left : Fin leftCount -> α)
    (right : Fin rightCount -> α)
    (predicate : α -> Prop) :
    (Semantics.matchingIndices (Fin.append left right) predicate).card =
      (Semantics.matchingIndices left predicate).card +
        (Semantics.matchingIndices right predicate).card :=
  Semantics.matchingIndices_append_card left right predicate

/-- Canonical-routing compatibility theorem for matching-position counts
under an equality-of-lengths reindexing. -/
theorem matchingIndices_cast_card
    (sequence : Fin leftCount -> α)
    (predicate : α -> Prop)
    (countEquality : leftCount = rightCount) :
    (Semantics.matchingIndices
      (fun index : Fin rightCount =>
        sequence (Fin.cast countEquality.symm index)) predicate).card =
      (Semantics.matchingIndices sequence predicate).card :=
  Semantics.matchingIndices_cast_card sequence predicate countEquality

/-- Canonical-routing compatibility theorem identifying a unique sorted
value's index with the number of smaller entries. -/
theorem matchingIndices_lt_card_eq_index
    [LinearOrder κ]
    (sequence : Fin n -> κ)
    (increasing : Semantics.SequenceIncreasing sequence)
    (index : Fin n)
    (unique : forall other, sequence other = sequence index ->
      other = index) :
    (Semantics.matchingIndices sequence
      (fun value => value < sequence index)).card = index.val :=
  Semantics.matchingIndices_lt_card_eq_index sequence increasing index unique

/-! ## Rank of the complete active-destination block -/

/-- In the semantic source/destination/padding layout, exactly `target.val`
complemented headers lie below the active destination at canonical position
`target`.  Source tags exclude the source block; the reserved marker excludes
the padding block. -/
theorem routingRecordSequence_fullDest_header_count_lt
    (sourceKeys : Fin sourceCount -> Fin (baseWidth + 1) -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationPayloads : Fin (2 ^ baseWidth) ->
      Fin payloadWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin baseWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (target : Fin (2 ^ baseWidth)) :
    (Semantics.matchingIndices
      (fun record => complementedRecordHeader
        (Routing.routingRecordSequence sourceKeys sourcePayloads
          (fun destination => activeRoutingKey (lexBitVectorAt destination))
          destinationPayloads
          (fun padding => paddingRoutingKey (paddingTails padding))
          paddingPayloads record))
      (fun header => header <
        activeDestinationHeader (lexBitVectorAt target))).card =
      target.val := by
  classical
  let targetHeader := activeDestinationHeader (lexBitVectorAt target)
  let sourceRecords := fun source =>
    Routing.packRecord (sourceKeys source) false (sourcePayloads source)
  let destinationRecords := fun destination =>
    Routing.packRecord
      (activeRoutingKey (lexBitVectorAt destination)) true
      (destinationPayloads destination)
  let paddingRecords := fun padding =>
    Routing.packRecord (paddingRoutingKey (paddingTails padding)) true
      (paddingPayloads padding)
  have sourceCountZero :
      (Semantics.matchingIndices
        sourceRecords
        (fun record => complementedRecordHeader record < targetHeader)).card =
          0 := by
    unfold Semantics.matchingIndices
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro source _member
    exact complementedSourceHeader_not_lt_active (baseWidth := baseWidth)
      (sourceKeys source) (sourcePayloads source) (lexBitVectorAt target)
  have destinationFilter :
      Semantics.matchingIndices
          destinationRecords
          (fun record => complementedRecordHeader record < targetHeader) =
        Finset.Iio target := by
    ext destination
    simp only [Semantics.matchingIndices, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_Iio]
    change
      complementedRecordHeader
          (Routing.packRecord
            (activeRoutingKey (lexBitVectorAt destination)) true
            (destinationPayloads destination)) <
          activeDestinationHeader (lexBitVectorAt target) ↔
        destination < target
    rw [complementedActiveDestinationHeader_lt_iff]
    exact (lexBitVectorAt_strictMono
      (width := baseWidth)).lt_iff_lt
  have destinationCountValue :
      (Semantics.matchingIndices
        destinationRecords
        (fun record => complementedRecordHeader record < targetHeader)).card =
          target.val := by
    rw [destinationFilter]
    simp
  have paddingCountZero :
      (Semantics.matchingIndices
        paddingRecords
        (fun record => complementedRecordHeader record < targetHeader)).card =
          0 := by
    unfold Semantics.matchingIndices
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro padding _member
    exact complementedPaddingHeader_not_lt_active (baseWidth := baseWidth)
      (paddingTails padding) (paddingPayloads padding)
      (lexBitVectorAt target)
  unfold Routing.routingRecordSequence
  change
    (Semantics.matchingIndices
      (Fin.append (Fin.append sourceRecords destinationRecords)
        paddingRecords)
      (fun record => complementedRecordHeader record < targetHeader)).card =
        target.val
  rw [Semantics.matchingIndices_append_card,
    Semantics.matchingIndices_append_card,
    sourceCountZero, destinationCountValue, paddingCountZero]
  omega

/-- The same exact header-rank statement after flattening and casting the
semantic layout to the sorting network's power-of-two capacity. -/
theorem routingInputBits_fullDest_header_count_lt
    (sourceKeys : Fin sourceCount -> Fin (baseWidth + 1) -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationPayloads : Fin (2 ^ baseWidth) ->
      Fin payloadWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin baseWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + 2 ^ baseWidth + paddingCount =
      networkRecords depth)
    (target : Fin (2 ^ baseWidth)) :
    let input := Routing.routingInputBits sourceKeys sourcePayloads
      (fun destination => activeRoutingKey (lexBitVectorAt destination))
      destinationPayloads
      (fun padding => paddingRoutingKey (paddingTails padding))
      paddingPayloads recordCount
    (Semantics.matchingIndices
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun header => header <
        activeDestinationHeader (lexBitVectorAt target))).card =
      target.val := by
  dsimp only
  rw [Routing.flatRecords_routingInputBits]
  unfold Routing.networkRoutingRecords
  exact (Semantics.matchingIndices_cast_card
    (fun record => complementedRecordHeader
      (Routing.routingRecordSequence sourceKeys sourcePayloads
        (fun destination => activeRoutingKey (lexBitVectorAt destination))
        destinationPayloads
        (fun padding => paddingRoutingKey (paddingTails padding))
        paddingPayloads record))
    (fun header => header <
      activeDestinationHeader (lexBitVectorAt target)) recordCount).trans
    (routingRecordSequence_fullDest_header_count_lt sourceKeys
      sourcePayloads destinationPayloads paddingTails paddingPayloads target)

/-! ## Complete match-and-canonicalize pass -/

/-- Semantic composition of the first sort-and-copy pass with the canonical
tag-flip and second sort. -/
def matchedCanonicalRoutingBits
    (depth keyWidth payloadWidth : Nat)
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool :=
  canonicalSortBits depth keyWidth payloadWidth
    (Routing.predecessorCopyBits depth keyWidth payloadWidth false true
      (bitonicSortBits
        (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true input))

/-- Explicit two-sort routing circuit: match by `(key, tag)`, copy the source
payload, flip tags, then sort by `(tag, key)`. -/
def matchedCanonicalRoutingCircuit
    (depth keyWidth payloadWidth : Nat) :=
  (canonicalSortCircuit depth keyWidth payloadWidth).comp
    (Routing.sortedPredecessorCopyCircuit depth keyWidth payloadWidth
      false true)

@[simp] theorem matchedCanonicalRoutingCircuit_eval
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    (matchedCanonicalRoutingCircuit depth keyWidth payloadWidth).eval
        DeMorgan.interpretation input =
      matchedCanonicalRoutingBits depth keyWidth payloadWidth input := by
  rw [matchedCanonicalRoutingCircuit, Circuit.eval_comp,
    canonicalSortCircuit_eval,
    Routing.sortedPredecessorCopyCircuit_eval]
  rfl

theorem matchedCanonicalRoutingCircuit_cost_le :
    (matchedCanonicalRoutingCircuit depth keyWidth payloadWidth).cost
        DeMorgan.standardCost <=
      (depth * depth * networkRecords depth *
          ((2 * Routing.recordWidth keyWidth payloadWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4)) +
        networkBits depth (Routing.recordWidth keyWidth payloadWidth) *
          (12 * keyWidth + 12)) +
      (networkBits depth (Routing.recordWidth keyWidth payloadWidth) +
        depth * depth * networkRecords depth *
          ((2 * Routing.recordWidth keyWidth payloadWidth) *
            (2 * ((keyWidth + 1) * (6 * (keyWidth + 1) + 4)) + 4))) := by
  rw [matchedCanonicalRoutingCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (Routing.sortedPredecessorCopyCircuit_cost_le false true)
    canonicalSortCircuit_cost_le

/-- Header-level permutation invariant for the complete matching and
canonicalization pipeline. -/
theorem canonicalMatchedHeadersPermuteCore
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    let initiallySorted := bitonicSortBits
      (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true input
    let routed := Routing.predecessorCopyBits depth keyWidth payloadWidth
      false true initiallySorted
    let canonical := canonicalSortBits depth keyWidth payloadWidth routed
    Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords canonical record))
      (fun record => complementedRecordHeader (flatRecords input record)) := by
  dsimp only
  let initiallySorted := bitonicSortBits
    (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true input
  let routed := Routing.predecessorCopyBits depth keyWidth payloadWidth
    false true initiallySorted
  let complemented :=
    complementRoutingTagsBits depth keyWidth payloadWidth routed
  let canonical := canonicalSortBits depth keyWidth payloadWidth routed
  have canonicalRecords : FlatRecordsPermute canonical complemented := by
    exact canonicalSortBits_recordsPermute routed
  have first : Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords canonical record))
      (fun record => recordHeader (flatRecords complemented record)) := by
    have mapped := Semantics.SequencePermutes.map recordHeader canonicalRecords
    simpa [Function.comp_def] using mapped
  have middle :
      (fun record => recordHeader (flatRecords complemented record)) =
        (fun record => complementedRecordHeader
          (flatRecords initiallySorted record)) := by
    funext record
    simp [complemented, routed, complementedRecordHeader]
  have initiallySortedRecords : FlatRecordsPermute initiallySorted input := by
    exact bitonicSortBits_recordsPermute
      (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true input
  have second : Semantics.SequencePermutes
      (fun record => complementedRecordHeader
        (flatRecords initiallySorted record))
      (fun record => complementedRecordHeader
        (flatRecords input record)) := by
    have mapped := Semantics.SequencePermutes.map complementedRecordHeader
      initiallySortedRecords
    simpa [Function.comp_def] using mapped
  rw [middle] at first
  exact first.trans second

theorem complementedRecordHeader_eq_activeDestinationHeader_iff
    (record : Fin (Routing.recordWidth (baseWidth + 1) payloadWidth) -> Bool)
    (baseKey : Fin baseWidth -> Bool) :
    complementedRecordHeader record = activeDestinationHeader baseKey ↔
      Routing.recordHasKeyTag (activeRoutingKey baseKey) true record := by
  unfold complementedRecordHeader activeDestinationHeader
    Routing.recordHasKeyTag
  rw [toLex_inj, Fin.cons_inj]
  simp [and_comm]

theorem recordHasKeyTag_predecessorCopyBits_iff
    (sourceTag destinationTag : Bool)
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth))
    (key : Fin keyWidth -> Bool)
    (tag : Bool) :
    Routing.recordHasKeyTag key tag
        (flatRecords
          (Routing.predecessorCopyBits depth keyWidth payloadWidth
            sourceTag destinationTag input) record) ↔
      Routing.recordHasKeyTag key tag (flatRecords input record) := by
  simp [Routing.recordHasKeyTag]

theorem recordHeader_complement_eq_activeDestinationHeader_iff
    (input : Fin (networkBits depth
      (Routing.recordWidth (baseWidth + 1) payloadWidth)) -> Bool)
    (record : Fin (networkRecords depth))
    (baseKey : Fin baseWidth -> Bool) :
    recordHeader
        (flatRecords
          (complementRoutingTagsBits depth (baseWidth + 1) payloadWidth input)
          record) =
      activeDestinationHeader baseKey ↔
        Routing.recordHasKeyTag (activeRoutingKey baseKey) true
          (flatRecords input record) := by
  rw [recordHeader_complementRoutingTagsBits]
  exact complementedRecordHeader_eq_activeDestinationHeader_iff
    (flatRecords input record) baseKey

/-- Complete active-key-space destinations occupy fixed output positions:
position `target` contains exactly the destination with base key
`lexBitVectorAt target`. -/
theorem matchedCanonicalRoutingBits_fullDest_fixed_header
    (sourceKeys : Fin sourceCount -> Fin (baseWidth + 1) -> Bool)
    (sourcePayloads : Fin sourceCount -> Fin payloadWidth -> Bool)
    (destinationPayloads : Fin (2 ^ baseWidth) ->
      Fin payloadWidth -> Bool)
    (paddingTails : Fin paddingCount -> Fin baseWidth -> Bool)
    (paddingPayloads : Fin paddingCount -> Fin payloadWidth -> Bool)
    (recordCount : sourceCount + 2 ^ baseWidth + paddingCount =
      networkRecords depth)
    (target : Fin (2 ^ baseWidth)) :
    let input := Routing.routingInputBits sourceKeys sourcePayloads
      (fun destination => activeRoutingKey (lexBitVectorAt destination))
      destinationPayloads
      (fun padding => paddingRoutingKey (paddingTails padding))
      paddingPayloads recordCount
    let output := matchedCanonicalRoutingBits depth (baseWidth + 1)
      payloadWidth input
    let destinationFits : 2 ^ baseWidth <= networkRecords depth := by omega
    recordHeader
        (flatRecords output (Fin.castLE destinationFits target)) =
      activeDestinationHeader (lexBitVectorAt target) := by
  dsimp only
  let input := Routing.routingInputBits sourceKeys sourcePayloads
    (fun destination => activeRoutingKey (lexBitVectorAt destination))
    destinationPayloads
    (fun padding => paddingRoutingKey (paddingTails padding))
    paddingPayloads recordCount
  let output := matchedCanonicalRoutingBits depth (baseWidth + 1)
    payloadWidth input
  let targetHeader := activeDestinationHeader (lexBitVectorAt target)
  have destinationKeyInjective : Function.Injective
      (fun destination : Fin (2 ^ baseWidth) =>
        activeRoutingKey (lexBitVectorAt destination)) :=
    activeRoutingKey_injective.comp lexBitVectorAt_injective
  have paddingAvoids : forall padding destination,
      paddingRoutingKey (paddingTails padding) ≠
        activeRoutingKey (lexBitVectorAt destination) := by
    intro padding destination
    exact paddingRoutingKey_ne_activeRoutingKey _ _
  have uniqueInitialRecord := Routing.routingInputBits_unique_destination
    sourceKeys sourcePayloads
    (fun destination => activeRoutingKey (lexBitVectorAt destination))
    destinationPayloads
    (fun padding => paddingRoutingKey (paddingTails padding))
    paddingPayloads destinationKeyInjective paddingAvoids recordCount target
  have uniqueInitialHeader : Sorting.Semantics.UniqueIndexWhere
      (fun record => complementedRecordHeader (flatRecords input record))
      (fun header => header = targetHeader) := by
    obtain ⟨index, indexMatches, indexOnly⟩ := uniqueInitialRecord
    refine ⟨index, ?_, ?_⟩
    · exact (complementedRecordHeader_eq_activeDestinationHeader_iff
        (flatRecords input index) (lexBitVectorAt target)).mpr indexMatches
    · intro other otherMatches
      apply indexOnly other
      exact (complementedRecordHeader_eq_activeDestinationHeader_iff
        (flatRecords input other) (lexBitVectorAt target)).mp otherMatches
  have headersPermute : Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords output record))
      (fun record => complementedRecordHeader (flatRecords input record)) := by
    exact canonicalMatchedHeadersPermuteCore input
  have uniqueOutputHeader :=
    Sorting.Semantics.UniqueIndexWhere.of_sequencePermutes
    headersPermute uniqueInitialHeader
  obtain ⟨outputIndex, outputMatches, outputOnly⟩ := uniqueOutputHeader
  have outputIncreasing : Semantics.SequenceIncreasing
      (fun record => recordHeader (flatRecords output record)) := by
    have sorted := canonicalSortBits_keysSorted
      (Routing.predecessorCopyBits depth (baseWidth + 1) payloadWidth
        false true
        (bitonicSortBits
          (Routing.keyAndTagFitsRecord (baseWidth + 1) payloadWidth)
          depth true input))
    unfold FlatKeysSortedBy FlatKeysSorted Semantics.SequenceSorted at sorted
    simp only [ite_true] at sorted
    intro left right before
    have ordered := sorted left right before
    change
      flatRecordKey
          (Routing.keyAndTagFitsRecord (baseWidth + 1) payloadWidth)
          (flatRecords
            (reindexRecordBits
              (tagFirstBitOrder (baseWidth + 1) payloadWidth) output) left) <=
        flatRecordKey
          (Routing.keyAndTagFitsRecord (baseWidth + 1) payloadWidth)
          (flatRecords
            (reindexRecordBits
              (tagFirstBitOrder (baseWidth + 1) payloadWidth) output) right)
        at ordered
    rw [tagFirstVirtualKey output left, tagFirstVirtualKey output right]
      at ordered
    simpa only [recordHeader_flatRecords] using ordered
  have outputRank :
      (Semantics.matchingIndices
        (fun record => recordHeader (flatRecords output record))
        (fun header => header < targetHeader)).card = outputIndex.val := by
    rw [← outputMatches]
    apply Semantics.matchingIndices_lt_card_eq_index
      (fun record => recordHeader (flatRecords output record))
      outputIncreasing outputIndex
    intro other equal
    apply outputOnly other
    exact equal.trans outputMatches
  have initialRank :
      (Semantics.matchingIndices
        (fun record => complementedRecordHeader (flatRecords input record))
        (fun header => header < targetHeader)).card = target.val := by
    exact routingInputBits_fullDest_header_count_lt sourceKeys
      sourcePayloads destinationPayloads paddingTails paddingPayloads
      recordCount target
  have rankPreserved := headersPermute.matchingIndices_card_eq
    (fun header => header < targetHeader)
  have outputIndexValue : outputIndex.val = target.val := by
    exact outputRank.symm.trans (rankPreserved.trans initialRank)
  have destinationFits : 2 ^ baseWidth <= networkRecords depth := by
    omega
  have outputIndexEquality :
      outputIndex = Fin.castLE destinationFits target := by
    apply Fin.ext
    exact outputIndexValue
  rw [← outputIndexEquality]
  exact outputMatches

/-- The complete match, tag-flip, and canonical-sort pipeline permutes the
canonical headers of the initial records after tag complementation.  Payload
updates do not affect this statement. -/
theorem canonicalMatchedHeadersPermute
    (input : Fin (networkBits depth
      (Routing.recordWidth keyWidth payloadWidth)) -> Bool) :
    let initiallySorted := bitonicSortBits
      (Routing.keyAndTagFitsRecord keyWidth payloadWidth) depth true input
    let routed := Routing.predecessorCopyBits depth keyWidth payloadWidth
      false true initiallySorted
    let canonical := canonicalSortBits depth keyWidth payloadWidth routed
    Semantics.SequencePermutes
      (fun record => recordHeader (flatRecords canonical record))
      (fun record => complementedRecordHeader (flatRecords input record)) := by
  exact canonicalMatchedHeadersPermuteCore input

end CanonicalRouting
end MassProduction
end Algebraic
