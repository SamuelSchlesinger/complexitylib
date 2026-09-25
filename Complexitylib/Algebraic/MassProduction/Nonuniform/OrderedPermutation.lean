/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingSemantics
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.FinRange

/-!
# Uniqueness of sorted finite sequences

A sorted permutation of an already sorted identifier sequence is pointwise
equal to that sequence. Distinct identifiers therefore restore literal
output positions after a data-dependent sorting pass.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform

open Sorting.Semantics

/-- Increasing permutations agree at every position, including repetitions. -/
theorem increasingPermutations_eq
    {Key : Type*} [LinearOrder Key]
    {left right : Fin count → Key}
    (permuted : SequencePermutes left right)
    (leftSorted : SequenceIncreasing left) (rightSorted : SequenceIncreasing right) :
    left = right := by
  have leftPairwise : (List.ofFn left).Pairwise (· ≤ ·) := by
    rw [List.pairwise_ofFn]
    exact leftSorted
  have rightPairwise : (List.ofFn right).Pairwise (· ≤ ·) := by
    rw [List.pairwise_ofFn]
    exact rightSorted
  exact List.ofFn_injective (List.Perm.eq_of_pairwise' leftPairwise rightPairwise permuted)

/-- When input records are distinct, a record permutation is realized by
an actual permutation of positions. Identifiers provide this distinctness. -/
theorem existsIndexPermutation
    {Record : Type*} {output input : Fin count → Record}
    (permuted : SequencePermutes output input) (distinct : Function.Injective input) :
    ∃ indices : Equiv.Perm (Fin count), ∀ index, output index = input (indices index) := by
  classical
  have outputDistinct : Function.Injective output := List.nodup_ofFn.mp
    (permuted.nodup_iff.mpr (List.nodup_ofFn.mpr distinct))
  let indices : Fin count → Fin count := fun index =>
    Classical.choose (permuted.rangeContained index)
  have recordsEqual : ∀ index, output index = input (indices index) := fun index =>
    Classical.choose_spec (permuted.rangeContained index)
  have indicesInjective : Function.Injective indices := by
    intro left right sameIndex
    apply outputDistinct
    exact (recordsEqual left).trans ((congrArg input sameIndex).trans (recordsEqual right).symm)
  exact ⟨Equiv.ofBijective indices
    ⟨indicesInjective, Finite.surjective_of_injective indicesInjective⟩, recordsEqual⟩

/-- Sorting, attaching marks, and sorting by preserved distinct identifiers
restore every original position. The two index permutations are inverse. -/
theorem restoredIndexPermutations
    {Record Marked Identifier : Type*} [LinearOrder Identifier]
    (body : Marked → Record) (identifier : Record → Identifier)
    (input sorted : Fin count → Record) (marked output : Fin count → Marked)
    (firstPermutes : SequencePermutes sorted input)
    (bodyPreserved : ∀ index, body (marked index) = sorted index)
    (lastPermutes : SequencePermutes output marked)
    (initiallyOrdered : StrictMono (fun index => identifier (input index)))
    (finallyOrdered : SequenceIncreasing (fun index => identifier (body (output index)))) :
    ∃ first last : Equiv.Perm (Fin count),
      (∀ index, sorted index = input (first index)) ∧
      (∀ index, output index = marked (last index)) ∧
      ∀ index, first (last index) = index := by
  have inputDistinct : Function.Injective input := by
    intro left right equalRecords
    exact initiallyOrdered.injective (congrArg identifier equalRecords)
  obtain ⟨first, firstRecords⟩ := existsIndexPermutation firstPermutes inputDistinct
  have markedDistinct : Function.Injective marked := by
    intro left right equalRecords
    have sameBody := congrArg body equalRecords
    rw [bodyPreserved, bodyPreserved, firstRecords, firstRecords] at sameBody
    exact first.injective (inputDistinct sameBody)
  obtain ⟨last, lastRecords⟩ := existsIndexPermutation lastPermutes markedDistinct
  have labels (index : Fin count) :
      identifier (body (output index)) = identifier (input (first (last index))) := by
    rw [lastRecords, bodyPreserved, firstRecords]
  have labelsPermute : SequencePermutes
      (fun index => identifier (body (output index)))
      (fun index => identifier (input index)) := by
    have known := Equiv.Perm.ofFn_comp_perm (last.trans first)
      (fun index => identifier (input index))
    simpa only [SequencePermutes, Function.comp_def, Equiv.trans_apply, ← labels] using known
  have sameLabels := increasingPermutations_eq labelsPermute finallyOrdered
    (fun left right before => (initiallyOrdered before).le)
  refine ⟨first, last, firstRecords, lastRecords, ?_⟩
  intro index
  exact initiallyOrdered.injective ((labels index).symm.trans (congrFun sameLabels index))

end Algebraic.MassProduction.Nonuniform
