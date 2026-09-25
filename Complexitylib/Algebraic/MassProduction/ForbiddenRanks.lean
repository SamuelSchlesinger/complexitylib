/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.DirectProduct
public import Complexitylib.Algebraic.MassProduction.FreshDirection
public import Complexitylib.Algebraic.MassProduction.Scheduler

/-!
# Guarded ranks for forbidden projective directions

The greedy scheduler forms difference vectors between the current target and
previously occupied recovery points.  A nonzero difference forbids its
projective direction; a zero difference forbids nothing.  This module gives
an explicit Boolean circuit for the fixed-width operation

* zero vector `->` the invalid projective-rank sentinel;
* nonzero vector `->` its canonical projective block rank.

It then replicates that circuit over a power-of-two packed array.  Padding by
zero vectors therefore becomes padding by the sentinel automatically.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace ForbiddenRanks

open scoped LinearAlgebra.Projectivization
open Sorting
open LeastMissing

/-- The raw vector is the first half of the postprocessor input. -/
def rawVectorBit
    (vectorWidth : Nat)
    (input : Fin (2 * vectorWidth) -> Bool)
    (bit : Fin vectorWidth) : Bool :=
  input (finProdFinEquiv ((0 : Fin 2), bit))

/-- The already-computed rank is the second half of the postprocessor
input. -/
def computedRankBit
    (vectorWidth : Nat)
    (input : Fin (2 * vectorWidth) -> Bool)
    (bit : Fin vectorWidth) : Bool :=
  input (finProdFinEquiv ((1 : Fin 2), bit))

/-- Test whether every bit in the raw-vector half is zero. -/
def rawVectorZeroExpression
    (vectorWidth : Nat) : DeMorgan.Expression (2 * vectorWidth) :=
  DeMorgan.Expression.finAnd vectorWidth fun bit =>
    .not (.input (finProdFinEquiv ((0 : Fin 2), bit)))

@[simp] theorem rawVectorZeroExpression_eval_eq_true_iff
    (input : Fin (2 * vectorWidth) -> Bool) :
    (rawVectorZeroExpression vectorWidth).eval input = true ↔
      ∀ bit, rawVectorBit vectorWidth input bit = false := by
  rw [rawVectorZeroExpression, DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  apply forall_congr'
  intro bit
  unfold rawVectorBit
  generalize valueEquality :
    input (finProdFinEquiv ((0 : Fin 2), bit)) = value
  cases value <;> simp [DeMorgan.Expression.eval, valueEquality]

/-- Select the sentinel on a zero raw vector and the computed rank
otherwise. -/
def guardedRankOutputExpression
    (dimension width : Nat)
    (output : Fin (dimension * width)) :
    DeMorgan.Expression (2 * (dimension * width)) :=
  muxExpression (rawVectorZeroExpression (dimension * width))
    (.constant (projectiveRankSentinel dimension width output))
    (.input (finProdFinEquiv ((1 : Fin 2), output)))

@[simp] theorem guardedRankOutputExpression_eval
    (input : Fin (2 * (dimension * width)) -> Bool)
    (output : Fin (dimension * width)) :
    (guardedRankOutputExpression dimension width output).eval input =
      if (rawVectorZeroExpression (dimension * width)).eval input then
        projectiveRankSentinel dimension width output
      else computedRankBit (dimension * width) input output := by
  rw [guardedRankOutputExpression, muxExpression_eval]
  rfl

theorem rawVectorZeroExpression_standardCost :
    (rawVectorZeroExpression vectorWidth).standardCost = 2 * vectorWidth := by
  rw [rawVectorZeroExpression,
    DeMorgan.Expression.finAnd_standardCost]
  simp [DeMorgan.Expression.standardCost]
  omega

theorem guardedRankOutputExpression_standardCost_le
    (output : Fin (dimension * width)) :
    (guardedRankOutputExpression dimension width output).standardCost ≤
      4 * (dimension * width) + 4 := by
  unfold guardedRankOutputExpression muxExpression
  simp only [DeMorgan.Expression.standardCost]
  rw [rawVectorZeroExpression_standardCost]
  omega

/-- Gate count of one independently compiled guarded output bit. -/
@[reducible] def guardedRankOutputGateCount
    (dimension width : Nat)
    (output : Fin (dimension * width)) : Nat :=
  (guardedRankOutputExpression dimension width output).gateCount

/-- Postprocess a `(raw vector, computed rank)` pair. -/
def guardedRankPostprocessCircuit
    (dimension width : Nat) :
    Circuit DeMorgan.signature (2 * (dimension * width))
      (dimension * width) :=
  Circuit.parallelFin (dimension * width) fun output =>
      (guardedRankOutputExpression dimension width output).circuit

@[simp] theorem guardedRankPostprocessCircuit_size
    (dimension width : Nat) :
    (guardedRankPostprocessCircuit dimension width).size =
      ∑ output, guardedRankOutputGateCount dimension width output := by
  simp [guardedRankPostprocessCircuit, guardedRankOutputGateCount]

@[simp] theorem guardedRankPostprocessCircuit_eval
    (input : Fin (2 * (dimension * width)) -> Bool)
    (output : Fin (dimension * width)) :
    (guardedRankPostprocessCircuit dimension width).eval
        DeMorgan.interpretation input output =
      if (rawVectorZeroExpression (dimension * width)).eval input then
        projectiveRankSentinel dimension width output
      else computedRankBit (dimension * width) input output := by
  rw [guardedRankPostprocessCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval,
    guardedRankOutputExpression_eval]

theorem guardedRankPostprocessCircuit_cost_le :
    (guardedRankPostprocessCircuit dimension width).cost
        DeMorgan.standardCost ≤
      (dimension * width) * (4 * (dimension * width) + 4) := by
  rw [guardedRankPostprocessCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    ∑ output : Fin (dimension * width),
        (guardedRankOutputExpression dimension width output).standardCost ≤
      ∑ _output : Fin (dimension * width),
        (4 * (dimension * width) + 4) := by
      exact Finset.sum_le_sum fun output _ =>
        guardedRankOutputExpression_standardCost_le output
    _ = (dimension * width) * (4 * (dimension * width) + 4) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]

/-- Preserve the raw vector alongside the projective rank computed from
it. -/
noncomputable def rawAndProjectiveRankCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :=
  (Circuit.id DeMorgan.signature (dimension * width)).parallelPair
    (projectiveDirectionRankCircuit dimension widthPositive)

@[simp] theorem rawAndProjectiveRankCircuit_raw
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool)
    (bit : Fin (dimension * width)) :
    (rawAndProjectiveRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation input
        (finProdFinEquiv ((0 : Fin 2), bit)) = input bit := by
  rw [rawAndProjectiveRankCircuit, Circuit.eval_parallelPair_apply,
    Circuit.eval_id]
  rfl

@[simp] theorem rawAndProjectiveRankCircuit_rank
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool)
    (bit : Fin (dimension * width)) :
    (rawAndProjectiveRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation input
        (finProdFinEquiv ((1 : Fin 2), bit)) =
      (projectiveDirectionRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation input bit := by
  rw [rawAndProjectiveRankCircuit, Circuit.eval_parallelPair_apply]
  rfl

@[simp] theorem rawAndProjectiveRankCircuit_cost
    (widthPositive : 0 < width) :
    (rawAndProjectiveRankCircuit dimension widthPositive).cost
        DeMorgan.standardCost =
      (projectiveDirectionRankCircuit dimension widthPositive).cost
        DeMorgan.standardCost := by
  simp [rawAndProjectiveRankCircuit]

theorem rawVectorZero_after_rawAndRank_iff
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool) :
    (rawVectorZeroExpression (dimension * width)).eval
        ((rawAndProjectiveRankCircuit dimension widthPositive).eval
          DeMorgan.interpretation input) = true ↔
      input = fun _ => false := by
  rw [rawVectorZeroExpression_eval_eq_true_iff]
  constructor
  · intro allZero
    funext bit
    have atBit := allZero bit
    rw [rawVectorBit, rawAndProjectiveRankCircuit_raw] at atBit
    exact atBit
  · intro inputZero bit
    rw [rawVectorBit, rawAndProjectiveRankCircuit_raw, inputZero]

/-- Rank one vector, mapping the zero vector to the sentinel. -/
noncomputable def guardedProjectiveRankCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :=
  (guardedRankPostprocessCircuit dimension width).comp
    (rawAndProjectiveRankCircuit dimension widthPositive)

@[simp] theorem guardedProjectiveRankCircuit_eval_zero
    (widthPositive : 0 < width) :
    (guardedProjectiveRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation (fun _ => false) =
      projectiveRankSentinel dimension width := by
  funext output
  rw [guardedProjectiveRankCircuit, Circuit.eval_comp,
    guardedRankPostprocessCircuit_eval]
  have zeroFlag := (rawVectorZero_after_rawAndRank_iff
    widthPositive (fun _ : Fin (dimension * width) => false)).mpr rfl
  simp [zeroFlag]

/-- On a nonzero packed vector, guarded ranking agrees with the complete
normalizer-plus-ranker circuit. -/
theorem guardedProjectiveRankCircuit_eval_of_ne_zero
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool)
    (inputNonzero : input ≠ fun _ => false) :
    (guardedProjectiveRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation input =
      (projectiveDirectionRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation input := by
  funext output
  rw [guardedProjectiveRankCircuit, Circuit.eval_comp,
    guardedRankPostprocessCircuit_eval]
  have zeroFlagFalse :
      (rawVectorZeroExpression (dimension * width)).eval
        ((rawAndProjectiveRankCircuit dimension widthPositive).eval
          DeMorgan.interpretation input) = false := by
    cases flagEquality :
        (rawVectorZeroExpression (dimension * width)).eval
          ((rawAndProjectiveRankCircuit dimension widthPositive).eval
            DeMorgan.interpretation input)
    · rfl
    · exact (inputNonzero ((rawVectorZero_after_rawAndRank_iff
        widthPositive input).mp flagEquality)).elim
  rw [zeroFlagFalse]
  exact rawAndProjectiveRankCircuit_rank widthPositive input output

/-- Every nonzero packed vector is guarded-ranked by its actual projective
direction. -/
theorem guardedProjectiveRankCircuit_eval_direction
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin (dimension * width) -> Bool)
    (inputNonzero : input ≠ fun _ => false) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (guardedProjectiveRankCircuit dimension widthPositive).eval
          DeMorgan.interpretation input =
        projectiveDirectionRankBits widthPositive direction := by
  let vector := binaryExtensionVectorCoordinate widthPositive input
  have vectorBits : binaryExtensionVectorBits widthPositive vector = input :=
    binaryExtensionVectorBits_vectorCoordinate widthPositive input
  have vectorNonzero : vector ≠ 0 := by
    intro vectorZero
    apply inputNonzero
    rw [← vectorBits, vectorZero]
    funext output
    unfold binaryExtensionVectorBits
    simp only [Pi.zero_apply]
    rw [decodeBinaryExtension_zero_bits]
    rfl
  let direction := Projectivization.mk (BinaryExtension width)
    vector vectorNonzero
  refine ⟨direction, ?_⟩
  rw [guardedProjectiveRankCircuit_eval_of_ne_zero
    widthPositive input inputNonzero]
  rw [← vectorBits]
  rw [projectiveDirectionRankCircuit, Circuit.eval_comp,
    normalizeBinaryExtensionVectorCircuit_eval_vectorBits
      widthPositive widthAtLeastTwo vector vectorNonzero,
    projectiveRankPackedCircuit_eval]
  unfold projectiveDirectionRankBits
  rw [projectiveDirectionKey_mk widthPositive vector vectorNonzero]

/-- A guarded rank lies below the projective sentinel exactly when its raw
packed vector is nonzero. -/
theorem guardedProjectiveRankCircuit_lt_sentinel_iff
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin (dimension * width) -> Bool) :
    toLex ((guardedProjectiveRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation input) <
        toLex (projectiveRankSentinel dimension width) ↔
      input ≠ fun _ => false := by
  constructor
  · intro below inputZero
    rw [inputZero, guardedProjectiveRankCircuit_eval_zero] at below
    exact (lt_irrefl _ below)
  · intro inputNonzero
    obtain ⟨direction, rankEquality⟩ :=
      guardedProjectiveRankCircuit_eval_direction
        widthPositive widthAtLeastTwo input inputNonzero
    rw [rankEquality]
    exact projectiveDirectionRankBits_lt_sentinel
      widthPositive direction

/-- On explicitly encoded nonzero field vectors, guarded ranking is exactly
the rank of the projective class of that vector. -/
theorem guardedProjectiveRankCircuit_eval_vectorBits
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (vector : Fin dimension -> BinaryExtension width)
    (vectorNonzero : vector ≠ 0) :
    (guardedProjectiveRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (binaryExtensionVectorBits widthPositive vector) =
      projectiveDirectionRankBits widthPositive
        (Projectivization.mk (BinaryExtension width) vector vectorNonzero) := by
  have bitsNonzero : binaryExtensionVectorBits widthPositive vector ≠
      (fun _ => false) := by
    intro bitsZero
    apply vectorNonzero
    funext coordinate
    rw [← binaryExtensionVectorCoordinate_vectorBits
      widthPositive vector coordinate]
    rw [bitsZero]
    unfold binaryExtensionVectorCoordinate
    rw [show (fun _ : Fin width => false) = 0 by rfl]
    exact encodeBinaryExtension_zero widthPositive
  rw [guardedProjectiveRankCircuit_eval_of_ne_zero
    widthPositive _ bitsNonzero]
  rw [projectiveDirectionRankCircuit, Circuit.eval_comp,
    normalizeBinaryExtensionVectorCircuit_eval_vectorBits
      widthPositive widthAtLeastTwo vector vectorNonzero,
    projectiveRankPackedCircuit_eval]
  unfold projectiveDirectionRankBits
  rw [projectiveDirectionKey_mk widthPositive vector vectorNonzero]

/-- Polynomial bound for sentinel-guarded normalization and ranking. -/
def guardedProjectiveRankCostBound
    (dimension width : Nat) : Nat :=
  projectiveNormalizationCircuitBound dimension width +
    (dimension * width) *
      (dimension * (width + 1 + dimension * (width + 2) + 2)) +
    (dimension * width) * (4 * (dimension * width) + 4)

theorem guardedProjectiveRankCircuit_cost_le
    (widthPositive : 0 < width) :
    (guardedProjectiveRankCircuit dimension widthPositive).cost
        DeMorgan.standardCost ≤
      guardedProjectiveRankCostBound dimension width := by
  unfold guardedProjectiveRankCircuit guardedProjectiveRankCostBound
  rw [Circuit.cost_comp, rawAndProjectiveRankCircuit_cost]
  exact Nat.add_le_add
    (projectiveDirectionRankCircuit_cost_le widthPositive)
    guardedRankPostprocessCircuit_cost_le

/-- Replicate guarded ranking over a power-of-two array of packed
vectors. -/
@[reducible] noncomputable def guardedProjectiveRankGateCount
    (dimension : Nat)
    (widthPositive : 0 < width) : Nat :=
  (guardedProjectiveRankCircuit dimension widthPositive).size

/-- Apply guarded projective ranking independently to every record in the
power-of-two array. -/
noncomputable def forbiddenRankArrayCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) :
    Circuit DeMorgan.signature
      (networkBits depth (dimension * width))
      (networkBits depth (dimension * width)) :=
  (guardedProjectiveRankCircuit dimension widthPositive).replicate
    (networkRecords depth)

@[simp] theorem forbiddenRankArrayCircuit_size
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) :
    (forbiddenRankArrayCircuit dimension widthPositive depth).size =
      networkRecords depth * guardedProjectiveRankGateCount dimension widthPositive := by
  simp [forbiddenRankArrayCircuit, guardedProjectiveRankGateCount]

@[simp] theorem forbiddenRankArrayCircuit_eval_apply
    (widthPositive : 0 < width)
    (depth : Nat)
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (record : Fin (networkRecords depth))
    (bit : Fin (dimension * width)) :
    (forbiddenRankArrayCircuit dimension widthPositive depth).eval
        DeMorgan.interpretation input
        (finProdFinEquiv (record, bit)) =
      (guardedProjectiveRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (directProductInput input record) bit := by
  exact Circuit.eval_replicate_apply
    (guardedProjectiveRankCircuit dimension widthPositive)
    (networkRecords depth) DeMorgan.interpretation input record bit

/-- Positions containing genuine nonzero difference vectors. -/
noncomputable def nonzeroVectorIndices
    (input : Fin (networkBits depth vectorWidth) -> Bool) :
    Finset (Fin (networkRecords depth)) := by
  classical
  exact Finset.univ.filter fun record =>
    directProductInput input record ≠ fun _ => false

/-- Guarded ranking sends exactly the zero-vector positions to the sentinel,
so the number of in-range ranks is the number of nonzero input blocks. -/
theorem inRangeRankIndices_forbiddenRankArray
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin (networkBits depth (dimension * width)) -> Bool) :
    inRangeRankIndices (projectiveRankSentinel dimension width)
        ((forbiddenRankArrayCircuit dimension widthPositive depth).eval
          DeMorgan.interpretation input) =
      nonzeroVectorIndices input := by
  classical
  ext record
  simp only [inRangeRankIndices, nonzeroVectorIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have rankAtEquality :
      rankAt
          ((forbiddenRankArrayCircuit dimension widthPositive depth).eval
            DeMorgan.interpretation input) record =
        (guardedProjectiveRankCircuit dimension widthPositive).eval
          DeMorgan.interpretation (directProductInput input record) := by
    funext bit
    exact forbiddenRankArrayCircuit_eval_apply
      widthPositive depth input record bit
  rw [rankAtEquality]
  exact guardedProjectiveRankCircuit_lt_sentinel_iff
    widthPositive widthAtLeastTwo (directProductInput input record)

/-- Replicated guarded-ranking cost bound. -/
def forbiddenRankArrayCostBound
    (dimension width depth : Nat) : Nat :=
  networkRecords depth * guardedProjectiveRankCostBound dimension width

theorem forbiddenRankArrayCircuit_cost_le
    (widthPositive : 0 < width) :
    (forbiddenRankArrayCircuit dimension widthPositive depth).cost
        DeMorgan.standardCost ≤
      forbiddenRankArrayCostBound dimension width depth := by
  unfold forbiddenRankArrayCostBound
  rw [show
    (forbiddenRankArrayCircuit dimension widthPositive depth).cost
        DeMorgan.standardCost =
      ((guardedProjectiveRankCircuit dimension widthPositive).replicate
        (networkRecords depth)).cost DeMorgan.standardCost by rfl]
  rw [Circuit.cost_replicate]
  exact Nat.mul_le_mul_left _
    (guardedProjectiveRankCircuit_cost_le widthPositive)

/-- One constructive scheduler stage: guarded-rank all forbidden difference
vectors, sort their ranks, choose a missing valid rank, and unrank it. -/
noncomputable def freshDirectionFromDifferencesCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) :=
  (FreshDirection.freshProjectiveDirectionCircuit
      dimension widthPositive depth).comp
    (forbiddenRankArrayCircuit dimension widthPositive depth)

/-- A scheduler stage returns a canonical direction key whose rank differs
from the guarded rank of every packed input vector.  Each nonzero input block
also comes with its actual forbidden projective direction and a proof that
the selected direction is different from it. -/
theorem freshDirectionFromDifferencesCircuit_sound_of_nonzero_capacity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (capacity : (nonzeroVectorIndices input).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (freshDirectionFromDifferencesCircuit
          dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      (∀ record : Fin (networkRecords depth),
        projectiveDirectionRankBits widthPositive direction ≠
          (guardedProjectiveRankCircuit dimension widthPositive).eval
            DeMorgan.interpretation
            (directProductInput input record)) ∧
      (∀ record : Fin (networkRecords depth),
        directProductInput input record ≠ (fun _ => false) ->
          ∃ forbiddenDirection : ℙ (BinaryExtension width)
              (Fin dimension -> BinaryExtension width),
            (guardedProjectiveRankCircuit dimension widthPositive).eval
                DeMorgan.interpretation
                (directProductInput input record) =
              projectiveDirectionRankBits widthPositive forbiddenDirection ∧
            direction ≠ forbiddenDirection) := by
  let forbiddenRanks :=
    (forbiddenRankArrayCircuit dimension widthPositive depth).eval
      DeMorgan.interpretation input
  have rankCapacity :
      (inRangeRankIndices (projectiveRankSentinel dimension width)
        forbiddenRanks).card <
        Nat.card (ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width)) := by
    rw [show inRangeRankIndices
        (projectiveRankSentinel dimension width) forbiddenRanks =
        nonzeroVectorIndices input by
      dsimp only [forbiddenRanks]
      exact inRangeRankIndices_forbiddenRankArray
        widthPositive widthAtLeastTwo input]
    exact capacity
  obtain ⟨direction, directionKey, rankMissing⟩ :=
    FreshDirection.freshProjectiveDirectionCircuit_sound_of_inRange_capacity
      widthPositive forbiddenRanks rankCapacity
  refine ⟨direction, ?_, ?_, ?_⟩
  · rw [freshDirectionFromDifferencesCircuit, Circuit.eval_comp]
    change (FreshDirection.freshProjectiveDirectionCircuit
      dimension widthPositive depth).eval DeMorgan.interpretation
        forbiddenRanks = projectiveDirectionKey widthPositive direction
    exact directionKey
  · intro record equalRank
    have forbiddenRankAt : rankAt forbiddenRanks record =
        (guardedProjectiveRankCircuit dimension widthPositive).eval
          DeMorgan.interpretation (directProductInput input record) := by
      funext bit
      change forbiddenRanks (finProdFinEquiv (record, bit)) = _
      dsimp only [forbiddenRanks]
      exact forbiddenRankArrayCircuit_eval_apply
        widthPositive depth input record bit
    apply rankMissing record
    rw [forbiddenRankAt]
    exact equalRank
  · intro record recordNonzero
    obtain ⟨forbiddenDirection, guardedEquality⟩ :=
      guardedProjectiveRankCircuit_eval_direction
        widthPositive widthAtLeastTwo (directProductInput input record)
          recordNonzero
    refine ⟨forbiddenDirection, guardedEquality, ?_⟩
    intro directionsEqual
    subst forbiddenDirection
    have forbiddenRankAt : rankAt forbiddenRanks record =
        (guardedProjectiveRankCircuit dimension widthPositive).eval
          DeMorgan.interpretation (directProductInput input record) := by
      funext bit
      change forbiddenRanks (finProdFinEquiv (record, bit)) = _
      dsimp only [forbiddenRanks]
      exact forbiddenRankArrayCircuit_eval_apply
        widthPositive depth input record bit
    apply rankMissing record
    rw [forbiddenRankAt, guardedEquality]

/-- Total-array capacity is a convenient sufficient condition for the
sentinel-aware scheduler theorem. -/
theorem freshDirectionFromDifferencesCircuit_sound
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (freshDirectionFromDifferencesCircuit
          dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      (∀ record : Fin (networkRecords depth),
        projectiveDirectionRankBits widthPositive direction ≠
          (guardedProjectiveRankCircuit dimension widthPositive).eval
            DeMorgan.interpretation
            (directProductInput input record)) ∧
      (∀ record : Fin (networkRecords depth),
        directProductInput input record ≠ (fun _ => false) ->
          ∃ forbiddenDirection : ℙ (BinaryExtension width)
              (Fin dimension -> BinaryExtension width),
            (guardedProjectiveRankCircuit dimension widthPositive).eval
                DeMorgan.interpretation
                (directProductInput input record) =
              projectiveDirectionRankBits widthPositive forbiddenDirection ∧
            direction ≠ forbiddenDirection) := by
  apply freshDirectionFromDifferencesCircuit_sound_of_nonzero_capacity
    widthPositive widthAtLeastTwo input
  calc
    (nonzeroVectorIndices input).card ≤
        (Finset.univ : Finset (Fin (networkRecords depth))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = networkRecords depth := by simp
    _ < Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := capacity

/-- Polynomial cost bound for a scheduler stage once its difference array is
available. -/
def freshDirectionFromDifferencesCostBound
    (dimension width depth : Nat) : Nat :=
  forbiddenRankArrayCostBound dimension width depth +
    FreshDirection.freshProjectiveDirectionCostBound
      dimension width depth

theorem freshDirectionFromDifferencesCircuit_cost_le
    (widthPositive : 0 < width) :
    (freshDirectionFromDifferencesCircuit
        dimension widthPositive depth).cost DeMorgan.standardCost ≤
      freshDirectionFromDifferencesCostBound dimension width depth := by
  unfold freshDirectionFromDifferencesCircuit
  rw [Circuit.cost_comp]
  exact Nat.add_le_add
    (forbiddenRankArrayCircuit_cost_le widthPositive)
    (FreshDirection.freshProjectiveDirectionCircuit_cost_le widthPositive)

/-- A punctured line over the concrete binary extension field, using a local
finite enumeration rather than exporting another global typeclass
instance. -/
noncomputable def binaryExtensionPuncturedLine
    (target : Fin dimension -> BinaryExtension width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    Finset (Fin dimension -> BinaryExtension width) := by
  let _ := Fintype.ofFinite (BinaryExtension width)
  exact puncturedLine target direction

/-- Sentinel-aware geometric scheduler-stage correctness.  Zero padding does
not count against direction capacity. -/
theorem freshDirectionFromDifferencesCircuit_disjoint_of_nonzero_capacity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (target : Fin dimension -> BinaryExtension width)
    (used : Finset (Fin dimension -> BinaryExtension width))
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (covers : ∀ point, point ∈ used ->
      ∃ record : Fin (networkRecords depth),
        directProductInput input record =
          binaryExtensionVectorBits widthPositive (point - target))
    (capacity : (nonzeroVectorIndices input).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (freshDirectionFromDifferencesCircuit
          dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint (binaryExtensionPuncturedLine target direction) used := by
  let _ := Fintype.ofFinite (BinaryExtension width)
  obtain ⟨direction, directionKey, ranksAvoid, _⟩ :=
    freshDirectionFromDifferencesCircuit_sound_of_nonzero_capacity
      widthPositive widthAtLeastTwo input capacity
  refine ⟨direction, directionKey, ?_⟩
  change Disjoint (puncturedLine target direction) used
  apply puncturedLine_disjoint_of_avoids_differences
    target direction used
  intro point pointUsed pointDifferent equalDirection
  obtain ⟨record, recordEquality⟩ := covers point pointUsed
  apply ranksAvoid record
  rw [recordEquality]
  rw [guardedProjectiveRankCircuit_eval_vectorBits
    widthPositive widthAtLeastTwo (point - target)
      (sub_ne_zero.mpr pointDifferent)]
  exact congrArg (projectiveDirectionRankBits widthPositive) equalDirection

/-- Geometric scheduler-stage correctness under the simpler total-array
capacity condition. -/
theorem freshDirectionFromDifferencesCircuit_disjoint
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (target : Fin dimension -> BinaryExtension width)
    (used : Finset (Fin dimension -> BinaryExtension width))
    (input : Fin (networkBits depth (dimension * width)) -> Bool)
    (covers : ∀ point, point ∈ used ->
      ∃ record : Fin (networkRecords depth),
        directProductInput input record =
          binaryExtensionVectorBits widthPositive (point - target))
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (freshDirectionFromDifferencesCircuit
          dimension widthPositive depth).eval
          DeMorgan.interpretation input =
        projectiveDirectionKey widthPositive direction ∧
      Disjoint (binaryExtensionPuncturedLine target direction) used := by
  apply freshDirectionFromDifferencesCircuit_disjoint_of_nonzero_capacity
    widthPositive widthAtLeastTwo target used input covers
  calc
    (nonzeroVectorIndices input).card ≤
        (Finset.univ : Finset (Fin (networkRecords depth))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = networkRecords depth := by simp
    _ < Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := capacity

end ForbiddenRanks
end MassProduction
end Algebraic
