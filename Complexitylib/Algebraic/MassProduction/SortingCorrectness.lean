/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingSemantics

/-!
# Correctness of the packed Boolean sorting circuit

This module bridges the explicit flat-bit Batcher circuit to the generic
record-level correctness theorem.  Keys are the initial `keyWidth` bits of
each record, ordered lexicographically; all remaining bits are payload and
must move with their record.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting

open Semantics

/-- View a flat row-major bit vector as a sequence of complete records. -/
def flatRecords
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    Fin (networkRecords depth) -> (Fin recordWidth -> Bool) :=
  fun record => networkRecord input record

/-- First-half record index with the successor-depth type made explicit. -/
def firstRecordIndex
    (depth : Nat)
    (pair : Fin (networkRecords depth)) :
    Fin (networkRecords (depth + 1)) :=
  ⟨pair.val, by
    rw [networkRecords]
    exact pair.isLt.trans_le (Nat.le_add_right _ _)⟩

/-- Second-half record index with the successor-depth type made explicit. -/
def secondRecordIndex
    (depth : Nat)
    (pair : Fin (networkRecords depth)) :
    Fin (networkRecords (depth + 1)) :=
  ⟨networkRecords depth + pair.val, by
    rw [networkRecords]
    omega⟩

private theorem firstRecordIndex_eq_castAdd
    (pair : Fin (networkRecords depth)) :
    firstRecordIndex depth pair =
      (Fin.castAdd (networkRecords depth) pair :
        Fin (networkRecords (depth + 1))) := by
  apply Fin.ext
  rfl

private theorem secondRecordIndex_eq_natAdd
    (pair : Fin (networkRecords depth)) :
    secondRecordIndex depth pair =
      (Fin.natAdd (networkRecords depth) pair :
        Fin (networkRecords (depth + 1))) := by
  apply Fin.ext
  rfl

/-- Lexicographic key carried by the initial bits of one record. -/
def flatRecordKey
    (keyFits : keyWidth <= recordWidth)
    (record : Fin recordWidth -> Bool) :
    Lex (Fin keyWidth -> Bool) :=
  toLex fun bit => record (Fin.castLE keyFits bit)

/-- Key-sortedness of a packed record array in the selected direction. -/
def FlatKeysSorted
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) : Prop :=
  SequenceSorted ascending
    (fun record => flatRecordKey keyFits (flatRecords input record))

/-- Preservation of all complete records, including payload bits. -/
def FlatRecordsPermute
    (output input : Fin (networkBits depth recordWidth) -> Bool) : Prop :=
  SequencePermutes (flatRecords output) (flatRecords input)

/-- Every output record of a complete-record permutation occurs in the input
record array. -/
theorem FlatRecordsPermute.rangeContained
    {output input : Fin (networkBits depth recordWidth) -> Bool}
    (permuted : FlatRecordsPermute output input) :
    SequenceRangeContained (flatRecords output) (flatRecords input) :=
  SequencePermutes.rangeContained permuted

/-- A complete-record permutation preserves unique satisfaction of every
record predicate. -/
theorem FlatRecordsPermute.uniqueIndexWhere
    {output input : Fin (networkBits depth recordWidth) -> Bool}
    {predicate : (Fin recordWidth -> Bool) -> Prop}
    (permuted : FlatRecordsPermute output input)
    (uniqueInput : UniqueIndexWhere (flatRecords input) predicate) :
    UniqueIndexWhere (flatRecords output) predicate :=
  UniqueIndexWhere.of_sequencePermutes permuted uniqueInput

private theorem flatRecords_firstHalfBits
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool) :
    flatRecords (firstHalfBits input) =
      recordFirstHalf (flatRecords input) := by
  funext record bit
  unfold flatRecords networkRecord firstHalfBits recordFirstHalf
  unfold firstHalfWire
  apply congrArg input
  apply Fin.ext
  rfl

private theorem flatRecords_secondHalfBits
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool) :
    flatRecords (secondHalfBits input) =
      recordSecondHalf (flatRecords input) := by
  funext record bit
  unfold flatRecords networkRecord secondHalfBits recordSecondHalf
  unfold secondHalfWire
  apply congrArg input
  apply Fin.ext
  simp [networkBits, finProdFinEquiv]
  change bit.val + recordWidth * record.val + 2 ^ depth * recordWidth =
    bit.val + recordWidth * (record.val + 2 ^ depth)
  ring

private theorem flatRecords_joinHalfBits
    (left right : Fin (networkBits depth recordWidth) -> Bool) :
    flatRecords (joinHalfBits left right) =
      joinRecordHalves (flatRecords left) (flatRecords right) := by
  funext record bit
  unfold flatRecords networkRecord joinHalfBits joinRecordHalves
  refine Fin.addCases (fun localRecord => ?_) (fun localRecord => ?_) record
  · simp only [Fin.append_left]
    have wireEquality :
        Fin.cast (networkBits_succ depth recordWidth)
            (finProdFinEquiv
              (Fin.castAdd (networkRecords depth) localRecord, bit)) =
          Fin.castAdd (networkBits depth recordWidth)
            (finProdFinEquiv (localRecord, bit)) := by
      apply Fin.ext
      rfl
    rw [wireEquality]
    exact Fin.append_left left right _
  · simp only [Fin.append_right]
    have wireEquality :
        Fin.cast (networkBits_succ depth recordWidth)
            (finProdFinEquiv
              (Fin.natAdd (networkRecords depth) localRecord, bit)) =
          Fin.natAdd (networkBits depth recordWidth)
            (finProdFinEquiv (localRecord, bit)) := by
      apply Fin.ext
      simp [networkBits, finProdFinEquiv]
      change bit.val + recordWidth * (localRecord.val + 2 ^ depth) =
        bit.val + recordWidth * localRecord.val + 2 ^ depth * recordWidth
      ring
    rw [wireEquality]
    exact Fin.append_right left right _

private theorem pairLeft_gatherLayer
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool)
    (pair : Fin (networkRecords depth)) :
    recordPairSide
        (input ∘ gatherLayerPairInput depth recordWidth pair) 0 =
      flatRecords input (firstRecordIndex depth pair) := by
  funext bit
  change input
      (gatherLayerPairInput depth recordWidth pair
        (recordPairIndex 0 bit)) =
    input (finProdFinEquiv
      (firstRecordIndex depth pair, bit))
  apply congrArg input
  simp only [networkBits]
  unfold gatherLayerPairInput recordPairIndex
  rw [Equiv.symm_apply_apply]
  dsimp only
  apply Fin.ext
  rfl

private theorem pairRight_gatherLayer
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool)
    (pair : Fin (networkRecords depth)) :
    recordPairSide
        (input ∘ gatherLayerPairInput depth recordWidth pair) 1 =
      flatRecords input (secondRecordIndex depth pair) := by
  funext bit
  change input
      (gatherLayerPairInput depth recordWidth pair
        (recordPairIndex 1 bit)) =
    input (finProdFinEquiv
      (secondRecordIndex depth pair, bit))
  apply congrArg input
  simp only [networkBits]
  unfold gatherLayerPairInput recordPairIndex
  rw [Equiv.symm_apply_apply]
  rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
  dsimp only
  simp only [networkBits]
  rw [Fin.cases_succ (i := (0 : Fin 1))]
  apply Fin.ext
  simp [finProdFinEquiv, secondRecordIndex,
    networkRecords_eq_two_pow]

@[simp] private theorem reverseRecordPairOutput_zero
    (bit : Fin recordWidth) :
    reverseRecordPairOutput (recordPairIndex 0 bit) =
      recordPairIndex 1 bit := by
  unfold reverseRecordPairOutput recordPairIndex
  rw [Equiv.symm_apply_apply]
  simp only [Fin.cases_zero]

@[simp] private theorem reverseRecordPairOutput_one
    (bit : Fin recordWidth) :
    reverseRecordPairOutput (recordPairIndex 1 bit) =
      recordPairIndex 0 bit := by
  unfold reverseRecordPairOutput recordPairIndex
  rw [Equiv.symm_apply_apply]
  rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
  congr 1

private theorem recordPairSide_comparePairBits_zero
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordPairSide (comparePairBits keyFits ascending input) 0 =
      if ascending then
        recordPairSide (compareSwapBits keyFits input) 0
      else recordPairSide (compareSwapBits keyFits input) 1 := by
  cases ascending with
  | false =>
      funext bit
      change compareSwapBits keyFits input
          (reverseRecordPairOutput (recordPairIndex 0 bit)) = _
      rw [reverseRecordPairOutput_zero]
      rfl
  | true => rfl

private theorem recordPairSide_comparePairBits_one
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordPairSide (comparePairBits keyFits ascending input) 1 =
      if ascending then
        recordPairSide (compareSwapBits keyFits input) 1
      else recordPairSide (compareSwapBits keyFits input) 0 := by
  cases ascending with
  | false =>
      funext bit
      change compareSwapBits keyFits input
          (reverseRecordPairOutput (recordPairIndex 1 bit)) = _
      rw [reverseRecordPairOutput_one]
      rfl
  | true => rfl

/-- The condition under which the left output selects the right record. -/
private def pairSelectsRight
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) : Bool :=
  if ascending then
    compareSwapFlag keyFits input
  else !(compareSwapFlag keyFits input)

private theorem compareSwapFlag_eq_false_iff
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool) :
    compareSwapFlag keyFits input = false ↔
      ¬toLex (recordKey keyFits input 1) <
        toLex (recordKey keyFits input 0) := by
  constructor
  · intro flagFalse rightLess
    have flagTrue := (compareSwapFlag_eq_true_iff keyFits input).mpr
      rightLess
    rw [flagFalse] at flagTrue
    contradiction
  · intro notLess
    cases flagEquality : compareSwapFlag keyFits input
    · rfl
    · exact False.elim
        (notLess ((compareSwapFlag_eq_true_iff keyFits input).mp
          flagEquality))

private theorem pairLeft_comparePairBits
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordPairSide (comparePairBits keyFits ascending input) 0 =
      if pairSelectsRight keyFits ascending input then
        recordPairSide input 1 else recordPairSide input 0 := by
  rw [recordPairSide_comparePairBits_zero]
  cases ascending with
  | false =>
      simp only [Bool.false_eq_true, ite_false, pairSelectsRight]
      rw [compareSwapBits_side_one]
      cases compareSwapFlag keyFits input <;> rfl
  | true =>
      simp only [ite_true, pairSelectsRight]
      exact compareSwapBits_side_zero keyFits input

private theorem pairRight_comparePairBits
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) :
    recordPairSide (comparePairBits keyFits ascending input) 1 =
      if pairSelectsRight keyFits ascending input then
        recordPairSide input 0 else recordPairSide input 1 := by
  rw [recordPairSide_comparePairBits_one]
  cases ascending with
  | false =>
      simp only [Bool.false_eq_true, ite_false, pairSelectsRight]
      rw [compareSwapBits_side_zero]
      cases compareSwapFlag keyFits input <;> rfl
  | true =>
      simp only [ite_true, pairSelectsRight]
      exact compareSwapBits_side_one keyFits input

private theorem pairSelectsRight_eq_true_iff
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (2 * recordWidth) -> Bool) :
    pairSelectsRight keyFits ascending input = true ↔
      if ascending then
        toLex (recordKey keyFits input 1) <
          toLex (recordKey keyFits input 0)
      else ¬toLex (recordKey keyFits input 1) <
          toLex (recordKey keyFits input 0) := by
  cases ascending with
  | false =>
      cases flagEquality : compareSwapFlag keyFits input with
      | false =>
          have notLess :=
            (compareSwapFlag_eq_false_iff keyFits input).mp flagEquality
          simp [pairSelectsRight, flagEquality, notLess]
      | true =>
          have rightLess :=
            (compareSwapFlag_eq_true_iff keyFits input).mp flagEquality
          simp [pairSelectsRight, flagEquality, rightLess]
  | true =>
      simp only [pairSelectsRight, ite_true]
      exact compareSwapFlag_eq_true_iff keyFits input

private theorem flatRecordKey_pairSide
    (keyFits : keyWidth <= recordWidth)
    (input : Fin (2 * recordWidth) -> Bool)
    (side : Fin 2) :
    flatRecordKey keyFits (recordPairSide input side) =
      toLex (recordKey keyFits input side) :=
  rfl

private theorem pairSelectsRight_gather_eq_true_iff
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool)
    (pair : Fin (networkRecords depth)) :
    pairSelectsRight keyFits ascending
        (input ∘ gatherLayerPairInput depth recordWidth pair) = true ↔
      if ascending then
        flatRecordKey keyFits
            (flatRecords input (secondRecordIndex depth pair)) <
          flatRecordKey keyFits
            (flatRecords input (firstRecordIndex depth pair))
      else
        ¬flatRecordKey keyFits
            (flatRecords input (secondRecordIndex depth pair)) <
          flatRecordKey keyFits
            (flatRecords input (firstRecordIndex depth pair)) := by
  rw [pairSelectsRight_eq_true_iff]
  cases ascending with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [← flatRecordKey_pairSide, ← flatRecordKey_pairSide,
        pairLeft_gatherLayer, pairRight_gatherLayer]
  | true =>
      simp only [ite_true]
      rw [← flatRecordKey_pairSide, ← flatRecordKey_pairSide,
        pairLeft_gatherLayer, pairRight_gatherLayer]

private theorem flatRecords_compareLayer_left
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool)
    (pair : Fin (networkRecords depth)) :
    flatRecords (compareLayerBits depth keyFits ascending input)
        (Fin.castAdd (networkRecords depth) pair) =
      recordPairSide
        (comparePairBits keyFits ascending
          (input ∘ gatherLayerPairInput depth recordWidth pair)) 0 := by
  funext bit
  unfold flatRecords networkRecord compareLayerBits recordPairSide
  dsimp only
  simp only [Equiv.symm_apply_apply]
  have firstHalf :
      (Fin.castAdd (networkRecords depth) pair).val <
        networkRecords depth := pair.isLt
  rw [dite_eq_left firstHalf]
  rfl

private theorem flatRecords_compareLayer_right
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool)
    (pair : Fin (networkRecords depth)) :
    flatRecords (compareLayerBits depth keyFits ascending input)
        (Fin.natAdd (networkRecords depth) pair) =
      recordPairSide
        (comparePairBits keyFits ascending
          (input ∘ gatherLayerPairInput depth recordWidth pair)) 1 := by
  funext bit
  unfold flatRecords networkRecord compareLayerBits recordPairSide
  dsimp only
  simp only [Equiv.symm_apply_apply]
  have notFirstHalf :
      ¬(Fin.natAdd (networkRecords depth) pair).val <
        networkRecords depth := by simp
  rw [dite_eq_right notFirstHalf]
  have pairEquality :
      (⟨(Fin.natAdd (networkRecords depth) pair).val -
          networkRecords depth, by simpa using pair.isLt⟩ :
        Fin (networkRecords depth)) = pair := by
    apply Fin.ext
    simp
  rw [pairEquality]

private theorem flatRecords_compareLayerBits
    (keyFits : keyWidth <= recordWidth)
    (ascending : Bool)
    (input : Fin (networkBits (depth + 1) recordWidth) -> Bool) :
    flatRecords (compareLayerBits depth keyFits ascending input) =
      keyedCompareLayer (flatRecordKey keyFits) depth ascending
        (flatRecords input) := by
  funext record
  refine Fin.addCases (fun pair => ?_) (fun pair => ?_) record
  · rw [flatRecords_compareLayer_left,
      pairLeft_comparePairBits, pairLeft_gatherLayer,
      pairRight_gatherLayer]
    unfold keyedCompareLayer keyedCompareSource
    dsimp only
    have firstHalf :
        (Fin.castAdd (networkRecords depth) pair).val <
          networkRecords depth := pair.isLt
    rw [dite_eq_left firstHalf]
    have pairEquality :
        (⟨(Fin.castAdd (networkRecords depth) pair).val, firstHalf⟩ :
          Fin (networkRecords depth)) = pair := by
      apply Fin.ext
      rfl
    simp only [pairEquality]
    rw [← firstRecordIndex_eq_castAdd,
      ← secondRecordIndex_eq_natAdd]
    rw [apply_ite (flatRecords input)]
    have selection := pairSelectsRight_gather_eq_true_iff
      keyFits ascending input pair
    cases selectionValue : pairSelectsRight keyFits ascending
        (input ∘ gatherLayerPairInput depth recordWidth pair) with
    | false =>
        have conditionFalse : ¬(if ascending then
            flatRecordKey keyFits
                (flatRecords input
                  (secondRecordIndex depth pair)) <
              flatRecordKey keyFits
                (flatRecords input
                  (firstRecordIndex depth pair))
          else
            ¬flatRecordKey keyFits
                (flatRecords input
                  (secondRecordIndex depth pair)) <
              flatRecordKey keyFits
                (flatRecords input
                  (firstRecordIndex depth pair))) := by
          intro conditionTrue
          have selected := selection.mpr conditionTrue
          rw [selectionValue] at selected
          contradiction
        simp only [Bool.false_eq_true, ite_false]
        exact (ite_eq_right conditionFalse).symm
    | true =>
        have conditionTrue := selection.mp selectionValue
        simp only [ite_true]
        exact (ite_eq_left conditionTrue).symm
  · rw [flatRecords_compareLayer_right,
      pairRight_comparePairBits, pairLeft_gatherLayer,
      pairRight_gatherLayer]
    unfold keyedCompareLayer keyedCompareSource
    dsimp only
    have notFirstHalf :
        ¬(Fin.natAdd (networkRecords depth) pair).val <
          networkRecords depth := by simp
    rw [dite_eq_right notFirstHalf]
    have pairEquality :
        (⟨(Fin.natAdd (networkRecords depth) pair).val -
            networkRecords depth, by simpa using pair.isLt⟩ :
          Fin (networkRecords depth)) = pair := by
      apply Fin.ext
      simp
    simp only [pairEquality]
    rw [← firstRecordIndex_eq_castAdd,
      ← secondRecordIndex_eq_natAdd]
    rw [apply_ite (flatRecords input)]
    have selection := pairSelectsRight_gather_eq_true_iff
      keyFits ascending input pair
    cases selectionValue : pairSelectsRight keyFits ascending
        (input ∘ gatherLayerPairInput depth recordWidth pair) with
    | false =>
        have conditionFalse : ¬(if ascending then
            flatRecordKey keyFits
                (flatRecords input
                  (secondRecordIndex depth pair)) <
              flatRecordKey keyFits
                (flatRecords input
                  (firstRecordIndex depth pair))
          else
            ¬flatRecordKey keyFits
                (flatRecords input
                  (secondRecordIndex depth pair)) <
              flatRecordKey keyFits
                (flatRecords input
                  (firstRecordIndex depth pair))) := by
          intro conditionTrue
          have selected := selection.mpr conditionTrue
          rw [selectionValue] at selected
          contradiction
        simp only [Bool.false_eq_true, ite_false]
        exact (ite_eq_right conditionFalse).symm
    | true =>
        have conditionTrue := selection.mp selectionValue
        simp only [ite_true]
        exact (ite_eq_left conditionTrue).symm

/-- The packed merge refines the generic keyed record merge. -/
theorem flatRecords_bitonicMergeBits
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    flatRecords (bitonicMergeBits keyFits depth ascending input) =
      keyedBitonicMerge (flatRecordKey keyFits) depth ascending
        (flatRecords input) := by
  induction depth generalizing ascending with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let compared := compareLayerBits depth keyFits ascending input
      have comparedEquality :
          flatRecords compared =
            keyedCompareLayer (flatRecordKey keyFits) depth ascending
              (flatRecords input) :=
        flatRecords_compareLayerBits keyFits ascending input
      rw [show bitonicMergeBits keyFits (depth + 1) ascending input =
          joinHalfBits
            (bitonicMergeBits keyFits depth ascending
              (firstHalfBits compared))
            (bitonicMergeBits keyFits depth ascending
              (secondHalfBits compared)) by rfl]
      rw [flatRecords_joinHalfBits, inductionHypothesis,
        inductionHypothesis, flatRecords_firstHalfBits,
        flatRecords_secondHalfBits, comparedEquality]
      rfl

/-- The packed sorter refines the generic keyed Batcher sorter. -/
theorem flatRecords_bitonicSortBits
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    flatRecords (bitonicSortBits keyFits depth ascending input) =
      keyedBitonicSort (flatRecordKey keyFits) depth ascending
        (flatRecords input) := by
  induction depth generalizing ascending with
  | zero => rfl
  | succ depth inductionHypothesis =>
      let first := firstHalfBits input
      let second := secondHalfBits input
      let prepared := joinHalfBits
        (bitonicSortBits keyFits depth true first)
        (bitonicSortBits keyFits depth false second)
      have preparedEquality :
          flatRecords prepared =
            joinRecordHalves
              (keyedBitonicSort (flatRecordKey keyFits) depth true
                (recordFirstHalf (flatRecords input)))
              (keyedBitonicSort (flatRecordKey keyFits) depth false
                (recordSecondHalf (flatRecords input))) := by
        dsimp only [prepared]
        rw [flatRecords_joinHalfBits, inductionHypothesis,
          inductionHypothesis, flatRecords_firstHalfBits,
          flatRecords_secondHalfBits]
      have merged := flatRecords_bitonicMergeBits keyFits (depth + 1)
        ascending prepared
      rw [preparedEquality] at merged
      simpa only [bitonicSortBits, keyedBitonicSort, prepared,
        first, second] using merged

/-- The explicit packed semantics sorts all record keys. -/
theorem bitonicSortBits_keysSorted
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatKeysSorted keyFits ascending
      (bitonicSortBits keyFits depth ascending input) := by
  unfold FlatKeysSorted
  rw [flatRecords_bitonicSortBits]
  exact keyedBitonicSort_sorted (flatRecordKey keyFits)
    depth ascending (flatRecords input)

/-- The explicit packed semantics preserves complete records up to
permutation. -/
theorem bitonicSortBits_recordsPermute
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatRecordsPermute
      (bitonicSortBits keyFits depth ascending input) input := by
  unfold FlatRecordsPermute
  rw [flatRecords_bitonicSortBits]
  exact keyedBitonicSort_permutes (flatRecordKey keyFits)
    depth ascending (flatRecords input)

/-- The evaluated Boolean circuit sorts every key in the chosen direction. -/
theorem bitonicSortCircuit_keysSorted
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatKeysSorted keyFits ascending
      ((bitonicSortCircuit keyFits depth ascending).eval
        DeMorgan.interpretation input) := by
  rw [bitonicSortCircuit_eval]
  exact bitonicSortBits_keysSorted keyFits depth ascending input

/-- The evaluated Boolean circuit permutes complete records and therefore
cannot separate a payload from its key. -/
theorem bitonicSortCircuit_recordsPermute
    (keyFits : keyWidth <= recordWidth)
    (depth : Nat)
    (ascending : Bool)
    (input : Fin (networkBits depth recordWidth) -> Bool) :
    FlatRecordsPermute
      ((bitonicSortCircuit keyFits depth ascending).eval
        DeMorgan.interpretation input) input := by
  rw [bitonicSortCircuit_eval]
  exact bitonicSortBits_recordsPermute keyFits depth ascending input

end Sorting
end MassProduction
end Algebraic
