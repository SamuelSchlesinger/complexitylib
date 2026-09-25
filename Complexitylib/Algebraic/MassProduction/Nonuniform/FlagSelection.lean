/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingCorrectness
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Selecting flagged records by sorting

Sorting a one-bit flag in decreasing order moves all flagged records to the
front while preserving complete records. A requested number of flagged
records can therefore be selected by fixed output wires, with no prefix
counter. This is the selection primitive for a halving scheduler phase.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.FlagSelection

open Sorting

/-- First bit of a record; remaining bits are carried as payload. -/
def flag
    (input : Fin (networkBits depth (1 + payloadWidth)) → Bool)
    (record : Fin (networkRecords depth)) : Bool :=
  input (finProdFinEquiv (record, (⟨0, by omega⟩ : Fin (1 + payloadWidth))))

/-- Sort by the first bit with flagged records first. -/
def circuit (depth payloadWidth : Nat) :=
  bitonicSortCircuit (by omega : 1 ≤ 1 + payloadWidth) depth false

/-- The one-bit key order is the ordinary order on Boolean flags. -/
theorem key_le_iff
    (input : Fin (networkBits depth (1 + payloadWidth)) → Bool)
    (left right : Fin (networkRecords depth)) :
    flatRecordKey (by omega : 1 ≤ 1 + payloadWidth) (flatRecords input left) ≤
      flatRecordKey (by omega : 1 ≤ 1 + payloadWidth) (flatRecords input right) ↔
        flag input left ≤ flag input right := by
  rw [Pi.lex_le_iff_of_unique]
  rfl

/-- The concrete sort puts true flags before false flags. -/
theorem circuit_flagsAntitone
    (input : Fin (networkBits depth (1 + payloadWidth)) → Bool) :
    Antitone (flag ((circuit depth payloadWidth).eval DeMorgan.interpretation input)) := by
  have sorted := bitonicSortCircuit_keysSorted
    (by omega : 1 ≤ 1 + payloadWidth) depth false input
  intro left right before
  rcases before.eq_or_lt with rfl | strict
  · exact le_rfl
  · exact (key_le_iff _ right left).mp (sorted left right strict)

set_option backward.isDefEq.respectTransparency false in
/-- Sorting preserves the number of flagged records exactly. -/
theorem circuit_flagCount
    (input : Fin (networkBits depth (1 + payloadWidth)) → Bool) :
    Nat.card {record : Fin (networkRecords depth) //
      flag ((circuit depth payloadWidth).eval DeMorgan.interpretation input) record = true} =
    Nat.card {record : Fin (networkRecords depth) // flag input record = true} := by
  classical
  have permuted := bitonicSortCircuit_recordsPermute
    (by omega : 1 ≤ 1 + payloadWidth) depth false input
  have counted := permuted.matchingIndices_card_eq
    (fun record : Fin (1 + payloadWidth) → Bool => record ⟨0, by omega⟩ = true)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Semantics.matchingIndices, flatRecords, networkRecord, flag, circuit] using counted

/-- In a decreasing Boolean sequence, every position below the count of
true entries is true. -/
theorem flag_true_of_lt_count
    (flags : Fin count → Bool) (ordered : Antitone flags) (index : Fin count)
    (enough : index.val < Nat.card {position : Fin count // flags position = true}) :
    flags index = true := by
  classical
  by_contra absent
  have isFalse : flags index = false := Bool.eq_false_iff.mpr absent
  have contained : (Finset.univ.filter fun position : Fin count => flags position = true) ⊆
      Finset.Iio index := by
    intro position membership
    have isTrue := (Finset.mem_filter.mp membership).2
    apply Finset.mem_Iio.mpr
    by_contra after
    have wrong := ordered (le_of_not_gt after)
    rw [isTrue, isFalse] at wrong
    exact (by decide : ¬ (true : Bool) ≤ false) wrong
  have atMost := Finset.card_le_card contained
  rw [Fin.card_Iio] at atMost
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at enough
  omega

/-- Fixed prefix positions select any requested number of available flagged
records. The actual complete records are preserved by the sorting network. -/
theorem circuit_selects
    (input : Fin (networkBits depth (1 + payloadWidth)) → Bool)
    (needed : Nat)
    (enough : needed ≤ Nat.card {record : Fin (networkRecords depth) // flag input record = true})
    (index : Fin (networkRecords depth)) (selected : index.val < needed) :
    flag ((circuit depth payloadWidth).eval DeMorgan.interpretation input) index = true := by
  apply flag_true_of_lt_count _ (circuit_flagsAntitone input) index
  rw [circuit_flagCount]
  exact selected.trans_le enough

/-- Complete records, including request identifiers, survive selection sorting. -/
theorem circuit_recordsPermute
    (input : Fin (networkBits depth (1 + payloadWidth)) → Bool) :
    FlatRecordsPermute
      ((circuit depth payloadWidth).eval DeMorgan.interpretation input) input :=
  bitonicSortCircuit_recordsPermute (by omega : 1 ≤ 1 + payloadWidth) depth false input

/-- If some record is flagged, the first output is a complete flagged input
record. Thus a flag sort also selects one successful candidate block. -/
theorem circuit_firstFlagged
    (input : Fin (networkBits depth (1 + payloadWidth)) → Bool)
    (available : ∃ record, flag input record = true) :
    ∃ source,
      flag input source = true ∧
      flatRecords ((circuit depth payloadWidth).eval DeMorgan.interpretation input)
          ⟨0, by simp⟩ = flatRecords input source := by
  classical
  have enough : 1 ≤ Nat.card {record : Fin (networkRecords depth) // flag input record = true} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr (by obtain ⟨record, flagged⟩ := available; exact ⟨record, flagged⟩)
  have firstTrue := circuit_selects input 1 enough ⟨0, by simp⟩ Nat.zero_lt_one
  obtain ⟨source, sameRecord⟩ := (circuit_recordsPermute input).rangeContained ⟨0, by simp⟩
  refine ⟨source, ?_, sameRecord⟩
  change flatRecords ((circuit depth payloadWidth).eval DeMorgan.interpretation input)
    ⟨0, by simp⟩ ⟨0, by omega⟩ = true at firstTrue
  rw [sameRecord] at firstTrue
  exact firstTrue

/-- Flag sorting costs at most forty-eight gates per record bit per squared
network depth. Its key width is one even for a large carried payload. -/
theorem circuit_cost_le :
    (circuit depth payloadWidth).cost DeMorgan.standardCost ≤
      48 * depth * depth * networkRecords depth * (1 + payloadWidth) := by
  have bound := bitonicSortCircuit_cost_le
    (by omega : 1 ≤ 1 + payloadWidth) depth false
  unfold circuit
  convert bound using 1
  ring

end Algebraic.MassProduction.Nonuniform.FlagSelection
