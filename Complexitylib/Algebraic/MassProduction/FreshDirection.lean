/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.LeastMissing
public import Complexitylib.Algebraic.MassProduction.ProjectiveRank

/-!
# Constructive selection of a fresh projective direction

This module joins the verified packed sorter, least-missing selector, and
projective unranker.  Its input is a power-of-two array of forbidden
projective ranks, with duplicates or unused positions optionally padded by
the projective sentinel.  Under the exact projective-capacity inequality it
returns the canonical packed vector of a direction whose rank occurs nowhere
in the input array.

The construction is the rank-selection core of the manuscript's greedy
scheduler.  Generation of the forbidden-rank array from prior recovery
points, and iteration of this core over all requested targets, are kept as
separate layers.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace FreshDirection

open scoped LinearAlgebra.Projectivization
open Sorting
open LeastMissing

/-- Sort a power-of-two array of packed ranks in ascending order. -/
def sortedRankBits
    (depth rankWidth : Nat)
    (input : Fin (networkBits depth rankWidth) -> Bool) :
    Fin (networkBits depth rankWidth) -> Bool :=
  bitonicSortBits (le_refl rankWidth) depth true input

/-- Pure semantics of selecting the least missing rank after sorting. -/
def freshProjectiveRankBits
    (dimension width depth : Nat)
    (input : Fin (networkBits depth (dimension * width)) -> Bool) :
    Fin (dimension * width) -> Bool :=
  leastMissingBits (projectiveRankSentinel dimension width) depth
    (sortedRankBits depth (dimension * width) input)

/-- Exact gate count of the input sorter followed by least-missing
selection. -/
@[reducible] def freshProjectiveRankGateCount
    (dimension width depth : Nat) : Nat :=
  bitonicSortGateCount (le_refl (dimension * width)) depth +
    leastMissingGateCount (projectiveRankSentinel dimension width) depth

/-- Explicit circuit selecting a fresh valid packed projective rank. -/
def freshProjectiveRankCircuit
    (dimension width depth : Nat) :
    Circuit DeMorgan.signature
      (networkBits depth (dimension * width))
      (freshProjectiveRankGateCount dimension width depth)
      (dimension * width) :=
  (leastMissingCircuit (projectiveRankSentinel dimension width) depth).comp
    (bitonicSortCircuit (le_refl (dimension * width)) depth true)

@[simp] theorem freshProjectiveRankCircuit_eval
    (input : Fin (networkBits depth (dimension * width)) -> Bool) :
    (freshProjectiveRankCircuit dimension width depth).eval
        DeMorgan.interpretation input =
      freshProjectiveRankBits dimension width depth input := by
  rw [freshProjectiveRankCircuit, Circuit.eval_comp,
    leastMissingCircuit_eval, bitonicSortCircuit_eval]
  rfl

/-- Sentinel-aware rank selection: only input records strictly below the
projective sentinel consume direction capacity. -/
theorem freshProjectiveRankCircuit_sound_of_inRange_capacity
    (widthPositive : 0 < width)
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (capacity :
      (inRangeRankIndices (projectiveRankSentinel dimension width)
        input).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    toLex ((freshProjectiveRankCircuit dimension width depth).eval
        DeMorgan.interpretation input) <
      toLex (projectiveRankSentinel dimension width) ∧
    ∀ index : Fin (networkRecords depth),
      (freshProjectiveRankCircuit dimension width depth).eval
          DeMorgan.interpretation input ≠ rankAt input index := by
  let sorted := sortedRankBits depth (dimension * width) input
  have sortedRanks :
      FlatKeysSorted (le_refl (dimension * width)) true sorted := by
    dsimp only [sorted, sortedRankBits]
    exact bitonicSortBits_keysSorted
      (le_refl (dimension * width)) depth true input
  have recordsPermute : FlatRecordsPermute sorted input := by
    dsimp only [sorted, sortedRankBits]
    exact bitonicSortBits_recordsPermute
      (le_refl (dimension * width)) depth true input
  have inRangeCount :
      (inRangeRankIndices (projectiveRankSentinel dimension width)
        sorted).card =
      (inRangeRankIndices (projectiveRankSentinel dimension width)
        input).card :=
    inRangeRankIndices_card_eq_of_recordsPermute
      (projectiveRankSentinel dimension width) recordsPermute
  have intervalCapacity :
      (inRangeRankIndices (projectiveRankSentinel dimension width)
        sorted).card <
      Nat.card {rank : Lex (Fin (dimension * width) -> Bool) //
        rank < toLex (projectiveRankSentinel dimension width)} := by
    rw [inRangeCount, card_projectiveRankInterval widthPositive]
    exact capacity
  have selectedSound := leastMissingBits_sound_of_inRange_capacity
    (projectiveRankSentinel dimension width) depth sorted sortedRanks
      intervalCapacity
  rw [freshProjectiveRankCircuit_eval]
  refine ⟨selectedSound.1, ?_⟩
  intro inputIndex selectedEqualsInput
  obtain ⟨sortedIndex, recordEquality⟩ :=
    flatRecordsPermute_exists_output_for_input
      recordsPermute inputIndex
  apply selectedSound.2 sortedIndex
  change leastMissingBits (projectiveRankSentinel dimension width) depth
    sorted = rankAt input inputIndex at selectedEqualsInput
  rw [selectedEqualsInput]
  simpa [rankAt, flatRecords] using recordEquality.symm

/-- Under the total-array direction-capacity inequality, rank selection
returns a valid projective rank absent from the original input array. -/
theorem freshProjectiveRankCircuit_sound
    (widthPositive : 0 < width)
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    toLex ((freshProjectiveRankCircuit dimension width depth).eval
        DeMorgan.interpretation input) <
      toLex (projectiveRankSentinel dimension width) ∧
    ∀ index : Fin (networkRecords depth),
      (freshProjectiveRankCircuit dimension width depth).eval
          DeMorgan.interpretation input ≠ rankAt input index := by
  apply freshProjectiveRankCircuit_sound_of_inRange_capacity
    widthPositive input
  calc
    (inRangeRankIndices (projectiveRankSentinel dimension width)
        input).card ≤
        (Finset.univ : Finset (Fin (networkRecords depth))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = networkRecords depth := by simp
    _ < Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := capacity

/-- Exact gate count after appending projective unranking. -/
@[reducible] noncomputable def freshProjectiveDirectionGateCount
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) : Nat :=
  freshProjectiveRankGateCount dimension width depth +
    (∑ output, projectiveUnrankBitGateCount dimension widthPositive output)

/-- Explicit circuit returning a canonical packed representative of a fresh
projective direction. -/
noncomputable def freshProjectiveDirectionCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) :
    Circuit DeMorgan.signature
      (networkBits depth (dimension * width))
      (freshProjectiveDirectionGateCount dimension widthPositive depth)
      (dimension * width) :=
  (projectiveUnrankPackedCircuit dimension widthPositive).comp
    (freshProjectiveRankCircuit dimension width depth)

/-- Sentinel-aware direction selection. -/
theorem freshProjectiveDirectionCircuit_sound_of_inRange_capacity
    (widthPositive : 0 < width)
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (capacity :
      (inRangeRankIndices (projectiveRankSentinel dimension width)
        input).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (freshProjectiveDirectionCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      ∀ index : Fin (networkRecords depth),
        projectiveDirectionRankBits widthPositive direction ≠
          rankAt input index := by
  have rankSound := freshProjectiveRankCircuit_sound_of_inRange_capacity
    widthPositive input capacity
  let selected := (freshProjectiveRankCircuit dimension width depth).eval
    DeMorgan.interpretation input
  have selectedLt : toLex selected <
      toLex (projectiveRankSentinel dimension width) := rankSound.1
  let direction :=
    projectiveDirectionOfRank widthPositive selected selectedLt
  refine ⟨direction, ?_, ?_⟩
  · rw [freshProjectiveDirectionCircuit, Circuit.eval_comp,
      projectiveUnrankPackedCircuit_eval]
    change projectiveUnrankPackedBits widthPositive selected =
      projectiveDirectionKey widthPositive direction
    simpa [direction] using
      (projectiveUnrankPackedBits_directionRank widthPositive direction)
  · intro index
    have selectedMissing : selected ≠ rankAt input index := by
      dsimp only [selected]
      exact rankSound.2 index
    rw [show projectiveDirectionRankBits widthPositive direction = selected by
      exact projectiveDirectionRankBits_directionOfRank
        widthPositive selected selectedLt]
    exact selectedMissing

/-- The direction circuit returns the canonical key of a projective
direction whose rank was not present in the input array. -/
theorem freshProjectiveDirectionCircuit_sound
    (widthPositive : 0 < width)
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (freshProjectiveDirectionCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      ∀ index : Fin (networkRecords depth),
        projectiveDirectionRankBits widthPositive direction ≠
          rankAt input index := by
  apply freshProjectiveDirectionCircuit_sound_of_inRange_capacity
    widthPositive input
  calc
    (inRangeRankIndices (projectiveRankSentinel dimension width)
        input).card ≤
        (Finset.univ : Finset (Fin (networkRecords depth))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = networkRecords depth := by simp
    _ < Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := capacity

/-- A uniform polynomial bound for sorting and least-missing selection. -/
def freshProjectiveRankCostBound
    (dimension width depth : Nat) : Nat :=
  depth * depth * networkRecords depth *
      ((2 * (dimension * width)) *
        (2 * ((dimension * width) *
          (6 * (dimension * width) + 4)) + 4)) +
    (networkBits depth
        (candidateRecordWidth (dimension * width)) *
          candidateOutputCostBound (dimension * width) +
      depth * depth * networkRecords depth *
        ((2 * candidateRecordWidth (dimension * width)) *
          (2 * (1 * (6 * 1 + 4)) + 4)))

/-- A uniform polynomial bound after appending projective unranking. -/
def freshProjectiveDirectionCostBound
    (dimension width depth : Nat) : Nat :=
  freshProjectiveRankCostBound dimension width depth +
    (dimension * width) *
      (dimension *
        (2 * width + 2 + dimension * (2 * width + 1) + 2))

/-- A uniform polynomial cost bound for the fresh-rank circuit. -/
theorem freshProjectiveRankCircuit_cost_le :
    (freshProjectiveRankCircuit dimension width depth).cost
        DeMorgan.standardCost ≤
      freshProjectiveRankCostBound dimension width depth := by
  unfold freshProjectiveRankCostBound
  rw [freshProjectiveRankCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (bitonicSortCircuit_cost_le
      (le_refl (dimension * width)) depth true)
    (leastMissingCircuit_cost_le
      (projectiveRankSentinel dimension width) depth)

/-- Appending unranking preserves a polynomial gate ledger. -/
theorem freshProjectiveDirectionCircuit_cost_le
    (widthPositive : 0 < width) :
    (freshProjectiveDirectionCircuit dimension widthPositive depth).cost
        DeMorgan.standardCost ≤
      freshProjectiveDirectionCostBound dimension width depth := by
  unfold freshProjectiveDirectionCostBound
  rw [freshProjectiveDirectionCircuit, Circuit.cost_comp]
  exact Nat.add_le_add freshProjectiveRankCircuit_cost_le
    (projectiveUnrankPackedCircuit_cost_le widthPositive)

end FreshDirection
end MassProduction
end Algebraic
