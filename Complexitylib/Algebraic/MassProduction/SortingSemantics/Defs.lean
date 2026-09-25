/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingNetwork
public import Mathlib.Data.List.OfFn

/-!
# Semantic model of Batcher sorting networks

This is the record-level semantic layer used to prove that the explicit
Boolean circuit sorts complete records by a projected key.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting
namespace Semantics

/-- Four-point lattice characterization of a bitonic sequence. -/
def SequenceBitonic {n : ℕ} [LinearOrder α] (sequence : Fin n → α) : Prop :=
  ∀ i j k l, i < j → j < k → k < l →
    min (sequence i) (sequence k) ≤ max (sequence j) (sequence l) ∧
      min (sequence j) (sequence l) ≤ max (sequence i) (sequence k)

/-- A sequence is increasing in its index order. -/
def SequenceIncreasing [LE α] {n : ℕ} (sequence : Fin n → α) : Prop :=
  ∀ i j, i < j → sequence i ≤ sequence j

/-- A sequence is decreasing in its index order. -/
def SequenceDecreasing [LE α] {n : ℕ} (sequence : Fin n → α) : Prop :=
  ∀ i j, i < j → sequence j ≤ sequence i

/-- Sortedness in the selected direction. -/
def SequenceSorted [LE α] {n : ℕ}
    (ascending : Bool) (sequence : Fin n → α) : Prop :=
  if ascending then SequenceIncreasing sequence
  else SequenceDecreasing sequence

/-- Every value of the first sequence is at most every value of the second. -/
def SequenceAllLE [LE α] {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α) : Prop :=
  ∀ i j, first i ≤ second j

/-- Every output value occurs somewhere in the input sequence. -/
def SequenceRangeContained {n m : ℕ}
    (output : Fin n → α) (input : Fin m → α) : Prop :=
  ∀ i, ∃ j, output i = input j

/-- The output sequence is a permutation of the input sequence. -/
def SequencePermutes {n : ℕ}
    (output input : Fin n → α) : Prop :=
  (List.ofFn output).Perm (List.ofFn input)

/-- Exactly one position of a finite sequence satisfies a predicate. -/
def UniqueIndexWhere
    (sequence : Fin n -> α)
    (predicate : α -> Prop) : Prop :=
  ∃ index, predicate (sequence index) ∧
    ∀ other, predicate (sequence other) -> other = index

/-- The positions of a finite sequence satisfying a predicate.  Classical
decidability is confined to the value of this definition. -/
noncomputable def matchingIndices
    (sequence : Fin n -> α)
    (predicate : α -> Prop) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun index => predicate (sequence index)

/-- Boolean reflection of a predicate, with the chosen decision procedure
kept out of theorem signatures. -/
noncomputable def predicateBit
    (predicate : α -> Prop) (value : α) : Bool := by
  classical
  exact decide (predicate value)

/-- Unique satisfaction is equivalent to the matching-position set having
cardinality one. -/
theorem UniqueIndexWhere.iff_matchingIndices_card_eq_one
    (sequence : Fin n -> α)
    (predicate : α -> Prop) :
    UniqueIndexWhere sequence predicate ↔
      (matchingIndices sequence predicate).card = 1 := by
  classical
  unfold matchingIndices
  constructor
  · rintro ⟨index, indexMatches, unique⟩
    apply Finset.card_eq_one.mpr
    refine ⟨index, ?_⟩
    ext other
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · exact unique other
    · intro equal
      subst other
      exact indexMatches
  · intro cardOne
    obtain ⟨index, filteredEquality⟩ := Finset.card_eq_one.mp cardOne
    have indexMember : predicate (sequence index) := by
      have : index ∈ Finset.univ.filter fun position =>
          predicate (sequence position) := by
        rw [filteredEquality]
        exact Finset.mem_singleton_self index
      simpa using this
    refine ⟨index, indexMember, ?_⟩
    intro other otherMatches
    have otherMember : other ∈ Finset.univ.filter fun position =>
        predicate (sequence position) := by
      simp [otherMatches]
    rw [filteredEquality] at otherMember
    simpa using otherMember

/-- Counting true predicate bits agrees with counting matching positions. -/
theorem countP_predicateBit_eq_matchingIndices_card
    (sequence : Fin n -> α)
    (predicate : α -> Prop) :
    (List.ofFn sequence).countP (predicateBit predicate) =
      (matchingIndices sequence predicate).card := by
  classical
  unfold predicateBit matchingIndices
  induction n with
  | zero => simp
  | succ prior inductionHypothesis =>
      rw [List.ofFn_succ, List.countP_cons]
      rw [Fin.card_filter_univ_succ']
      by_cases headMatches : predicate (sequence 0)
      · simp [headMatches,
          inductionHypothesis (fun index => sequence index.succ),
          Nat.add_comm]
      · simp [headMatches,
          inductionHypothesis (fun index => sequence index.succ)]

namespace SequenceRangeContained

/-- Range containment is transitive. -/
theorem trans {n m k : ℕ}
    {first : Fin n → α} {second : Fin m → α} {third : Fin k → α}
    (hfirst : SequenceRangeContained first second)
    (hsecond : SequenceRangeContained second third) :
    SequenceRangeContained first third := by
  intro i
  obtain ⟨j, hj⟩ := hfirst i
  obtain ⟨k, hk⟩ := hsecond j
  exact ⟨k, hj.trans hk⟩

end SequenceRangeContained

namespace SequencePermutes

/-- Every finite sequence is a permutation of itself. -/
theorem refl {n : ℕ} (input : Fin n → α) :
    SequencePermutes input input :=
  List.Perm.refl _

/-- Sequence permutation is transitive. -/
theorem trans {n : ℕ}
    {first second third : Fin n → α}
    (hfirst : SequencePermutes first second)
    (hsecond : SequencePermutes second third) :
    SequencePermutes first third :=
  List.Perm.trans hfirst hsecond

/-- Applying the same observation to two permuted finite sequences preserves
their permutation relation. -/
theorem map {n : ℕ} {output input : Fin n → α}
    (observe : α → β)
    (permuted : SequencePermutes output input) :
    SequencePermutes
      (fun index => observe (output index))
      (fun index => observe (input index)) := by
  unfold SequencePermutes at permuted ⊢
  rw [List.ofFn_comp' output observe, List.ofFn_comp' input observe]
  exact permuted.map observe

/-- Every output of a finite-sequence permutation is an input value. -/
theorem rangeContained {n : ℕ} {output input : Fin n -> α}
    (permuted : SequencePermutes output input) :
    SequenceRangeContained output input := by
  intro outputIndex
  have outputMember : output outputIndex ∈ List.ofFn output :=
    (List.mem_ofFn' output (output outputIndex)).mpr
      ⟨outputIndex, rfl⟩
  have inputMember : output outputIndex ∈ List.ofFn input :=
    permuted.mem_iff.mp outputMember
  obtain ⟨inputIndex, equality⟩ :=
    (List.mem_ofFn' input (output outputIndex)).mp inputMember
  exact ⟨inputIndex, equality.symm⟩

/-- A permutation preserves the number of positions satisfying a predicate. -/
theorem matchingIndices_card_eq {n : ℕ} {output input : Fin n -> α}
    (permuted : SequencePermutes output input)
    (predicate : α -> Prop) :
    (matchingIndices output predicate).card =
      (matchingIndices input predicate).card := by
  have counts := permuted.countP_eq (predicateBit predicate)
  rw [countP_predicateBit_eq_matchingIndices_card,
    countP_predicateBit_eq_matchingIndices_card] at counts
  exact counts

end SequencePermutes

namespace UniqueIndexWhere

/-- A sequence permutation preserves unique satisfaction of a predicate. -/
theorem of_sequencePermutes
    {output input : Fin n -> α}
    {predicate : α -> Prop}
    (permuted : SequencePermutes output input)
    (uniqueInput : UniqueIndexWhere input predicate) :
    UniqueIndexWhere output predicate := by
  rw [iff_matchingIndices_card_eq_one] at uniqueInput ⊢
  exact (permuted.matchingIndices_card_eq predicate).trans uniqueInput

/-- Reindexing a finite sequence along an equality of lengths preserves its
unique matching position. -/
theorem cast
    {sequence : Fin leftCount -> α}
    {predicate : α -> Prop}
    (unique : UniqueIndexWhere sequence predicate)
    (countEquality : leftCount = rightCount) :
    UniqueIndexWhere
      (fun index : Fin rightCount =>
        sequence (Fin.cast countEquality.symm index)) predicate := by
  obtain ⟨index, indexMatches, indexOnly⟩ := unique
  refine ⟨Fin.cast countEquality index, ?_, ?_⟩
  · simpa using indexMatches
  · intro other otherMatches
    have castEquality := indexOnly (Fin.cast countEquality.symm other)
      (by simpa using otherMatches)
    apply Fin.ext
    have valueEquality := congrArg Fin.val castEquality
    simpa using valueEquality

end UniqueIndexWhere

/-- Reindexing a finite sequence along an equality of lengths preserves the
number of matching positions. -/
theorem matchingIndices_cast_card
    (sequence : Fin leftCount -> α)
    (predicate : α -> Prop)
    (countEquality : leftCount = rightCount) :
    (matchingIndices
      (fun index : Fin rightCount =>
        sequence (Fin.cast countEquality.symm index)) predicate).card =
      (matchingIndices sequence predicate).card := by
  subst rightCount
  rfl

/-- Concatenation of two finite sequences. -/
def appendSequence {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α) : Fin (n + m) → α :=
  Fin.append first second

namespace UniqueIndexWhere

/-- A unique match in the left sequence remains unique after appending a
right sequence with no matches. -/
theorem append_left
    {left : Fin leftCount -> α}
    {right : Fin rightCount -> α}
    {predicate : α -> Prop}
    (uniqueLeft : UniqueIndexWhere left predicate)
    (noneRight : ∀ index, ¬predicate (right index)) :
    UniqueIndexWhere (Fin.append left right) predicate := by
  obtain ⟨leftIndex, leftMatches, leftOnly⟩ := uniqueLeft
  refine ⟨Fin.castAdd rightCount leftIndex, ?_, ?_⟩
  · simpa using leftMatches
  · intro other otherMatches
    refine Fin.addCases (motive := fun other =>
      predicate (Fin.append left right other) ->
        other = Fin.castAdd rightCount leftIndex)
      (fun leftOther => by
        intro hmatch
        have equalLeft := leftOnly leftOther (by simpa using hmatch)
        subst leftOther
        rfl)
      (fun rightOther => by
        intro hmatch
        exact False.elim (noneRight rightOther (by simpa using hmatch)))
      other otherMatches

/-- A unique match in the right sequence remains unique after prepending a
left sequence with no matches. -/
theorem append_right
    {left : Fin leftCount -> α}
    {right : Fin rightCount -> α}
    {predicate : α -> Prop}
    (noneLeft : ∀ index, ¬predicate (left index))
    (uniqueRight : UniqueIndexWhere right predicate) :
    UniqueIndexWhere (Fin.append left right) predicate := by
  obtain ⟨rightIndex, rightMatches, rightOnly⟩ := uniqueRight
  refine ⟨Fin.natAdd leftCount rightIndex, ?_, ?_⟩
  · simpa using rightMatches
  · intro other otherMatches
    refine Fin.addCases (motive := fun other =>
      predicate (Fin.append left right other) ->
        other = Fin.natAdd leftCount rightIndex)
      (fun leftOther => by
        intro hmatch
        exact False.elim (noneLeft leftOther (by simpa using hmatch)))
      (fun rightOther => by
        intro hmatch
        have equalRight := rightOnly rightOther (by simpa using hmatch)
        subst rightOther
        rfl)
      other otherMatches

end UniqueIndexWhere

/-- Matching positions in an appended sequence split additively. -/
theorem matchingIndices_append_card
    {α : Type*}
    (left : Fin leftCount -> α)
    (right : Fin rightCount -> α)
    (predicate : α -> Prop) :
    (matchingIndices (Fin.append left right) predicate).card =
      (matchingIndices left predicate).card +
        (matchingIndices right predicate).card := by
  rw [← countP_predicateBit_eq_matchingIndices_card
      (Fin.append left right) predicate,
    List.ofFn_fin_append, List.countP_append,
    countP_predicateBit_eq_matchingIndices_card left predicate,
    countP_predicateBit_eq_matchingIndices_card right predicate]

/-- In an increasing sequence, the index of a unique value equals the number
of sequence entries strictly below it. -/
theorem matchingIndices_lt_card_eq_index
    [LinearOrder κ]
    (sequence : Fin n -> κ)
    (increasing : SequenceIncreasing sequence)
    (index : Fin n)
    (unique : ∀ other, sequence other = sequence index -> other = index) :
    (matchingIndices sequence
      (fun value => value < sequence index)).card = index.val := by
  classical
  have filterEquality :
      matchingIndices sequence (fun value => value < sequence index) =
        Finset.Iio index := by
    ext other
    simp only [matchingIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iio]
    constructor
    · intro below
      by_contra notBefore
      have indexLeOther : index ≤ other := le_of_not_gt notBefore
      rcases indexLeOther.eq_or_lt with same | after
      · subst other
        exact lt_irrefl _ below
      · exact (not_le_of_gt below) (increasing index other after)
    · intro before
      have belowOrEqual := increasing other index before
      have different : sequence other ≠ sequence index := by
        intro equal
        exact (ne_of_lt before) (unique other equal)
      exact lt_of_le_of_ne belowOrEqual different
  rw [filterEquality]
  simp

namespace SequencePermutes

/-- Concatenating two pairs of permuted sequences preserves permutation. -/
theorem append {n m : ℕ}
    {first firstInput : Fin n → α} {second secondInput : Fin m → α}
    (hfirst : SequencePermutes first firstInput)
    (hsecond : SequencePermutes second secondInput) :
    SequencePermutes (appendSequence first second)
      (appendSequence firstInput secondInput) := by
  unfold SequencePermutes appendSequence at *
  simpa only [List.ofFn_fin_append] using hfirst.append hsecond

end SequencePermutes

/-- Pointwise minimum of equal-length sequences. -/
def pointwiseMin [LinearOrder α] {n : ℕ}
    (first second : Fin n → α) : Fin n → α :=
  fun i => min (first i) (second i)

/-- Pointwise maximum of equal-length sequences. -/
def pointwiseMax [LinearOrder α] {n : ℕ}
    (first second : Fin n → α) : Fin n → α :=
  fun i => max (first i) (second i)

/-- First half of a record-level network sequence. -/
def recordFirstHalf {depth : ℕ}
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords depth) → α :=
  fun index => input (Fin.castAdd (networkRecords depth) index)

/-- Second half of a record-level network sequence. -/
def recordSecondHalf {depth : ℕ}
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords depth) → α :=
  fun index => input (Fin.natAdd (networkRecords depth) index)

/-- Join two record-level half sequences. -/
def joinRecordHalves {depth : ℕ}
    (first second : Fin (networkRecords depth) → α) :
    Fin (networkRecords (depth + 1)) → α :=
  Fin.append first second

/-- The record-specific and general sequence append operations agree. -/
theorem appendSequence_eq_joinRecordHalves {depth : Nat}
    (first second : Fin (networkRecords depth) -> α) :
    appendSequence first second = joinRecordHalves first second :=
  rfl

/-- One record-level butterfly layer over a linear order. -/
def orderedCompareLayer [LinearOrder α] (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords (depth + 1)) → α :=
  let first := recordFirstHalf input
  let second := recordSecondHalf input
  if ascending then
    joinRecordHalves (pointwiseMin first second) (pointwiseMax first second)
  else
    joinRecordHalves (pointwiseMax first second) (pointwiseMin first second)

/-- Record-level bitonic merge over a linear order. -/
def orderedBitonicMerge [LinearOrder α] :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let compared := orderedCompareLayer depth ascending input
      joinRecordHalves
        (orderedBitonicMerge depth ascending (recordFirstHalf compared))
        (orderedBitonicMerge depth ascending (recordSecondHalf compared))

/-- Record-level Batcher sorter over a linear order. -/
def orderedBitonicSort [LinearOrder α] :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let prepared := joinRecordHalves
        (orderedBitonicSort depth true (recordFirstHalf input))
        (orderedBitonicSort depth false (recordSecondHalf input))
      orderedBitonicMerge (depth + 1) ascending prepared

/-- Source record selected for one output of a keyed compare layer. -/
noncomputable def keyedCompareSource [LinearOrder κ] (key : α → κ)
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α)
    (output : Fin (networkRecords (depth + 1))) :
    Fin (networkRecords (depth + 1)) :=
  let half := networkRecords depth
  if hleft : output.val < half then
    let pair : Fin half := ⟨output.val, hleft⟩
    let shouldSwap :=
      key (input (Fin.natAdd half pair)) <
        key (input (Fin.castAdd half pair))
    let sourceRight := if ascending then shouldSwap else ¬shouldSwap
    if sourceRight then Fin.natAdd half pair else Fin.castAdd half pair
  else
    let pair : Fin half := ⟨output.val - half, by
      have hbound : output.val < half + half := by
        simpa only [half, networkRecords_succ] using output.isLt
      omega⟩
    let shouldSwap :=
      key (input (Fin.natAdd half pair)) <
        key (input (Fin.castAdd half pair))
    let sourceRight := if ascending then shouldSwap else ¬shouldSwap
    if sourceRight then Fin.castAdd half pair else Fin.natAdd half pair

/-- One compare layer on records ordered only through a separate key. -/
noncomputable def keyedCompareLayer [LinearOrder κ] (key : α → κ)
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    Fin (networkRecords (depth + 1)) → α :=
  fun output => input (keyedCompareSource key depth ascending input output)

/-- Keyed record-level bitonic merge. -/
noncomputable def keyedBitonicMerge [LinearOrder κ] (key : α → κ) :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let compared := keyedCompareLayer key depth ascending input
      joinRecordHalves
        (keyedBitonicMerge key depth ascending (recordFirstHalf compared))
        (keyedBitonicMerge key depth ascending (recordSecondHalf compared))

/-- Keyed record-level Batcher sorter. -/
noncomputable def keyedBitonicSort [LinearOrder κ] (key : α → κ) :
    (depth : ℕ) → Bool →
      (Fin (networkRecords depth) → α) → Fin (networkRecords depth) → α
  | 0, _, input => input
  | depth + 1, ascending, input =>
      let prepared := joinRecordHalves
        (keyedBitonicSort key depth true (recordFirstHalf input))
        (keyedBitonicSort key depth false (recordSecondHalf input))
      keyedBitonicMerge key (depth + 1) ascending prepared

end Semantics
end Sorting
end MassProduction
end Algebraic
