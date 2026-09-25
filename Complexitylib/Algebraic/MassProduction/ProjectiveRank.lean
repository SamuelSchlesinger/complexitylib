/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.ProjectiveCircuit

/-!
# Packed ranks for projective directions

For a normalized nonzero vector with pivot `h`, the manuscript's block rank
is represented by `dimension` blocks of `width` bits:

* every block before `h` is the unsigned binary digit one;
* block `h` is the unsigned binary digit zero;
* every later block is the corresponding normalized field-coordinate bits.

With most-significant bits first this is exactly
`B_h + val_q(tail)`, but it avoids an addition circuit.  This module builds
the rank circuit after the existing projective normalizer, proves its exact
semantics, and supplies a polynomial cost ledger.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators
open scoped LinearAlgebra.Projectivization

/-- Big-endian `width`-bit representation of the unsigned integer one. -/
def unsignedOneBits (width : Nat) : Fin width -> Bool :=
  fun bit => decide (bit.val + 1 = width)

/-- Direct first-nonzero flag over packed field-coordinate bits. -/
def firstNonzeroDirectExpression
    (dimension width : Nat)
    (pivot : Fin dimension) :
    DeMorgan.Expression (dimension * width) :=
  .and (vectorCoordinateNonzeroExpression dimension width pivot)
    (DeMorgan.Expression.finAnd dimension fun previous =>
      if previous < pivot then
        .not (vectorCoordinateNonzeroExpression dimension width previous)
      else .constant true)

@[simp] theorem firstNonzeroDirectExpression_eval
    (input : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension) :
    (firstNonzeroDirectExpression dimension width pivot).eval input =
      firstNonzeroFlag (vectorCoordinateNonzeroFlags input) pivot := by
  rw [firstNonzeroDirectExpression, DeMorgan.Expression.eval,
    vectorCoordinateNonzeroExpression_eval,
    DeMorgan.Expression.finAnd_eval]
  unfold firstNonzeroFlag
  congr 1
  apply congrArg
  funext previous
  split_ifs <;>
    simp [DeMorgan.Expression.eval,
      vectorCoordinateNonzeroExpression_eval]

theorem firstNonzeroDirectExpression_vectorBits_eq_true_iff
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension) :
    (firstNonzeroDirectExpression dimension width pivot).eval
        (binaryExtensionVectorBits widthPositive vector) = true ↔
      firstNonzeroCoordinate vector = some pivot := by
  rw [firstNonzeroDirectExpression_eval]
  exact firstNonzeroFlag_vectorBits_eq_true_iff
    widthPositive vector pivot

/-- One rank bit selected after the pivot is known. -/
def rankValueExpression
    (dimension width : Nat)
    (coordinate : Fin dimension)
    (bit : Fin width)
    (pivot : Fin dimension) :
    DeMorgan.Expression (dimension * width) :=
  if coordinate < pivot then .constant (unsignedOneBits width bit)
  else if coordinate = pivot then .constant false
  else .input (finProdFinEquiv (coordinate, bit))

/-- One output bit of the packed projective rank. -/
def projectiveRankBitExpression
    (dimension width : Nat)
    (output : Fin (dimension * width)) :
    DeMorgan.Expression (dimension * width) :=
  let coordinateAndBit :=
    (finProdFinEquiv (m := dimension) (n := width)).symm output
  DeMorgan.Expression.finOr dimension fun pivot =>
    .and (firstNonzeroDirectExpression dimension width pivot)
      (rankValueExpression dimension width coordinateAndBit.1
        coordinateAndBit.2 pivot)

/-- Pure packed-bit semantics of the rank transformation. -/
def projectiveRankPackedBits
    (input : Fin (dimension * width) -> Bool) :
    Fin (dimension * width) -> Bool :=
  fun output => (projectiveRankBitExpression dimension width output).eval input

/-- Field-level block-rank representation when the pivot is known. -/
noncomputable def normalizedVectorRankBits
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension) :
    Fin (dimension * width) -> Bool :=
  fun output =>
    let coordinateAndBit :=
      (finProdFinEquiv (m := dimension) (n := width)).symm output
    if coordinateAndBit.1 < pivot then
      unsignedOneBits width coordinateAndBit.2
    else if coordinateAndBit.1 = pivot then false
    else decodeBinaryExtension widthPositive
      (vector coordinateAndBit.1) coordinateAndBit.2

theorem projectiveRankPackedBits_vectorBits
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension)
    (pivotEquality : firstNonzeroCoordinate vector = some pivot) :
    projectiveRankPackedBits
        (binaryExtensionVectorBits widthPositive vector) =
      normalizedVectorRankBits widthPositive vector pivot := by
  funext output
  unfold projectiveRankPackedBits projectiveRankBitExpression
  rw [DeMorgan.Expression.finOr_eval]
  let coordinateAndBit :=
    (finProdFinEquiv (m := dimension) (n := width)).symm output
  change DeMorgan.Expression.finOrValue dimension (fun selected =>
      (firstNonzeroDirectExpression dimension width selected).eval
          (binaryExtensionVectorBits widthPositive vector) &&
        (rankValueExpression dimension width coordinateAndBit.1
          coordinateAndBit.2 selected).eval
          (binaryExtensionVectorBits widthPositive vector)) = _
  rw [DeMorgan.Expression.finOrValue_oneHot dimension pivot]
  · unfold normalizedVectorRankBits rankValueExpression
    dsimp only [coordinateAndBit]
    split_ifs <;>
      simp [DeMorgan.Expression.eval, binaryExtensionVectorBits]
  · exact
      (firstNonzeroDirectExpression_vectorBits_eq_true_iff
        widthPositive vector pivot).mpr pivotEquality
  · intro selected selectedTrue
    have selectedEquality :=
      (firstNonzeroDirectExpression_vectorBits_eq_true_iff
        widthPositive vector selected).mp selectedTrue
    exact Option.some.inj (selectedEquality.symm.trans pivotEquality)

/-- Canonical block-rank key of a projective direction. -/
noncomputable def projectiveDirectionRankBits
    (widthPositive : 0 < width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    Fin (dimension * width) -> Bool :=
  projectiveRankPackedBits (projectiveDirectionKey widthPositive direction)

/-- One `width`-bit block of a packed rank. -/
def projectiveRankBlock
    (rank : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) : Fin width -> Bool :=
  fun bit => rank (finProdFinEquiv (coordinate, bit))

/-- First rank block different from the unsigned digit one.  Valid ranks have
one-blocks before the pivot and a zero-block at the pivot. -/
noncomputable def firstNonOneRankBlock
    (rank : Fin (dimension * width) -> Bool) : Option (Fin dimension) := by
  classical
  exact if existsDifferent : ∃ coordinate,
      projectiveRankBlock rank coordinate ≠ unsignedOneBits width then
    some (Fin.find (fun coordinate =>
      projectiveRankBlock rank coordinate ≠ unsignedOneBits width)
      existsDifferent)
  else none

theorem firstNonOneRankBlock_eq_some_iff
    (rank : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension) :
    firstNonOneRankBlock rank = some pivot ↔
      projectiveRankBlock rank pivot ≠ unsignedOneBits width ∧
        ∀ previous, previous < pivot ->
          projectiveRankBlock rank previous = unsignedOneBits width := by
  classical
  unfold firstNonOneRankBlock
  split_ifs with existsDifferent
  · simp only [Option.some.injEq]
    constructor
    · intro equal
      subst pivot
      exact ⟨Fin.find_spec existsDifferent, fun previous previousLt =>
        not_ne_iff.mp (Fin.find_min existsDifferent previousLt)⟩
    · rintro ⟨pivotDifferent, previousOne⟩
      apply Fin.ext
      by_contra different
      have ordered :
          Fin.find (fun coordinate =>
              projectiveRankBlock rank coordinate ≠ unsignedOneBits width)
              existsDifferent < pivot ∨
            pivot < Fin.find (fun coordinate =>
              projectiveRankBlock rank coordinate ≠ unsignedOneBits width)
              existsDifferent := by
        omega
      rcases ordered with findBefore | pivotBefore
      · exact (Fin.find_spec existsDifferent)
          (previousOne _ findBefore)
      · exact (Fin.find_min existsDifferent pivotBefore) pivotDifferent
  · constructor
    · intro impossible
      cases impossible
    · rintro ⟨pivotDifferent, _⟩
      exact (existsDifferent ⟨pivot, pivotDifferent⟩).elim

@[simp] theorem projectiveRankBlock_normalized_before
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot coordinate : Fin dimension)
    (before : coordinate < pivot) :
    projectiveRankBlock
        (normalizedVectorRankBits widthPositive vector pivot) coordinate =
      unsignedOneBits width := by
  funext bit
  simp [projectiveRankBlock, normalizedVectorRankBits, before]

@[simp] theorem projectiveRankBlock_normalized_pivot
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension) :
    projectiveRankBlock
        (normalizedVectorRankBits widthPositive vector pivot) pivot =
      fun _ => false := by
  funext bit
  simp [projectiveRankBlock, normalizedVectorRankBits]

theorem falseBits_ne_unsignedOneBits
    (widthPositive : 0 < width) :
    (fun _ : Fin width => false) ≠ unsignedOneBits width := by
  intro equal
  let finalBit : Fin width := ⟨width - 1, by omega⟩
  have atFinal := congrFun equal finalBit
  simp [unsignedOneBits, finalBit] at atFinal
  exact atFinal (by omega)

theorem firstNonOneRankBlock_normalizedVectorRankBits
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension) :
    firstNonOneRankBlock
        (normalizedVectorRankBits widthPositive vector pivot) = some pivot := by
  apply (firstNonOneRankBlock_eq_some_iff _ pivot).mpr
  constructor
  · rw [projectiveRankBlock_normalized_pivot]
    exact falseBits_ne_unsignedOneBits widthPositive
  · intro previous previousBefore
    exact projectiveRankBlock_normalized_before
      widthPositive vector pivot previous previousBefore

/-- Semantic inverse of the packed rank on valid ranks.  The first non-one
block identifies the pivot; earlier field coordinates are zero, the pivot is
field one, and later coordinates are copied from the rank tail. -/
noncomputable def projectiveUnrankPackedBits
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool) :
    Fin (dimension * width) -> Bool :=
  match firstNonOneRankBlock rank with
  | none => fun _ => false
  | some pivot => fun output =>
      let coordinateAndBit :=
        (finProdFinEquiv (m := dimension) (n := width)).symm output
      if coordinateAndBit.1 < pivot then false
      else if coordinateAndBit.1 = pivot then
        decodeBinaryExtension widthPositive
          (1 : BinaryExtension width) coordinateAndBit.2
      else rank output

/-- Unranking inverts ranking for any vector already normalized at its first
nonzero coordinate. -/
theorem projectiveUnrankPackedBits_rank_of_pivot
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension)
    (pivotEquality : firstNonzeroCoordinate vector = some pivot)
    (pivotOne : vector pivot = 1) :
    projectiveUnrankPackedBits widthPositive
        (projectiveRankPackedBits
          (binaryExtensionVectorBits widthPositive vector)) =
      binaryExtensionVectorBits widthPositive vector := by
  rw [projectiveRankPackedBits_vectorBits
    widthPositive vector pivot pivotEquality]
  unfold projectiveUnrankPackedBits
  rw [firstNonOneRankBlock_normalizedVectorRankBits]
  simp only
  funext output
  obtain ⟨⟨coordinate, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := dimension) (n := width)).surjective output
  rw [Equiv.symm_apply_apply]
  have pivotProperties :=
    (firstNonzeroCoordinate_eq_some_iff vector pivot).mp pivotEquality
  by_cases before : coordinate < pivot
  · rw [ite_eq_left before]
    unfold binaryExtensionVectorBits
    simp only [Equiv.symm_apply_apply]
    rw [pivotProperties.2 coordinate before]
    rw [decodeBinaryExtension_zero_bits]
    rfl
  · rw [ite_eq_right before]
    by_cases atPivot : coordinate = pivot
    · rw [ite_eq_left atPivot]
      subst coordinate
      unfold binaryExtensionVectorBits
      simp only [Equiv.symm_apply_apply]
      rw [pivotOne]
    · rw [ite_eq_right atPivot]
      simp [normalizedVectorRankBits, binaryExtensionVectorBits,
        before, atPivot]

/-- Projective normalization keeps the first nonzero coordinate. -/
theorem firstNonzeroCoordinate_normalizeBinaryExtensionVector
    (vector : Fin dimension -> BinaryExtension width)
    (vectorNonzero : vector ≠ 0) :
    firstNonzeroCoordinate (normalizeBinaryExtensionVector vector) =
      firstNonzeroCoordinate vector := by
  classical
  have existsNonzero : ∃ coordinate, vector coordinate ≠ 0 := by
    by_contra noneNonzero
    apply vectorNonzero
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp noneNonzero coordinate)
  let pivot :=
    Fin.find (fun coordinate => vector coordinate ≠ 0) existsNonzero
  have pivotEquality : firstNonzeroCoordinate vector = some pivot := by
    simp [firstNonzeroCoordinate, existsNonzero, pivot]
  have pivotNonzero :=
    (firstNonzeroCoordinate_eq_some_iff vector pivot).mp pivotEquality |>.1
  rw [normalizeBinaryExtensionVector_eq_of_firstNonzeroCoordinate
    vector pivot pivotEquality]
  exact firstNonzeroCoordinate_smul vector (vector pivot)⁻¹
    (inv_ne_zero pivotNonzero) existsNonzero

/-- The pivot coordinate of a normalized vector is field one. -/
theorem normalizeBinaryExtensionVector_pivot
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension)
    (pivotEquality : firstNonzeroCoordinate vector = some pivot) :
    normalizeBinaryExtensionVector vector pivot = 1 := by
  rw [normalizeBinaryExtensionVector_eq_of_firstNonzeroCoordinate
    vector pivot pivotEquality]
  exact inv_mul_cancel₀
    ((firstNonzeroCoordinate_eq_some_iff vector pivot).mp pivotEquality |>.1)

/-- Semantic unranking recovers the canonical normalized key of every
projective direction. -/
theorem projectiveUnrankPackedBits_directionRank
    (widthPositive : 0 < width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    projectiveUnrankPackedBits widthPositive
        (projectiveDirectionRankBits widthPositive direction) =
      projectiveDirectionKey widthPositive direction := by
  classical
  let vector := direction.rep
  have vectorNonzero : vector ≠ 0 := direction.rep_nonzero
  have existsNonzero : ∃ coordinate, vector coordinate ≠ 0 := by
    by_contra noneNonzero
    apply vectorNonzero
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp noneNonzero coordinate)
  let pivot :=
    Fin.find (fun coordinate => vector coordinate ≠ 0) existsNonzero
  have pivotEquality : firstNonzeroCoordinate vector = some pivot := by
    simp [firstNonzeroCoordinate, existsNonzero, pivot]
  let normalized := normalizeBinaryExtensionVector vector
  have normalizedPivot :
      firstNonzeroCoordinate normalized = some pivot := by
    rw [firstNonzeroCoordinate_normalizeBinaryExtensionVector
      vector vectorNonzero]
    exact pivotEquality
  have normalizedPivotOne : normalized pivot = 1 :=
    normalizeBinaryExtensionVector_pivot vector pivot pivotEquality
  unfold projectiveDirectionRankBits projectiveDirectionKey
  exact projectiveUnrankPackedBits_rank_of_pivot widthPositive
    normalized pivot normalizedPivot normalizedPivotOne

/-- The packed block rank is injective on projective directions. -/
theorem projectiveDirectionRankBits_injective
    (widthPositive : 0 < width) :
    Function.Injective
      (projectiveDirectionRankBits widthPositive :
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width) ->
        (Fin (dimension * width) -> Bool)) := by
  intro left right ranksEqual
  apply projectiveDirectionKey_injective widthPositive
  rw [← projectiveUnrankPackedBits_directionRank widthPositive left,
    ranksEqual,
    projectiveUnrankPackedBits_directionRank widthPositive right]

/-! ## The exact initial interval of valid projective ranks -/

/-- First invalid packed projective rank: one field digit in every block. -/
def projectiveRankSentinel (dimension width : Nat) :
    Fin (dimension * width) -> Bool :=
  fun output =>
    unsignedOneBits width
      ((finProdFinEquiv (m := dimension) (n := width)).symm output).2

@[simp] theorem projectiveRankSentinel_block
    (coordinate : Fin dimension) :
    projectiveRankBlock (projectiveRankSentinel dimension width) coordinate =
      unsignedOneBits width := by
  funext bit
  simp [projectiveRankBlock, projectiveRankSentinel]

/-- A normalized block rank is strictly below the all-one-digit sentinel. -/
theorem normalizedVectorRankBits_lt_sentinel
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension) :
    toLex (normalizedVectorRankBits widthPositive vector pivot) <
      toLex (projectiveRankSentinel dimension width) := by
  let last : Fin width := ⟨width - 1, by omega⟩
  let witness : Fin (dimension * width) :=
    finProdFinEquiv (pivot, last)
  refine ⟨witness, ?_, ?_⟩
  · intro previous previousLt
    obtain ⟨⟨coordinate, bit⟩, rfl⟩ :=
      (finProdFinEquiv (m := dimension) (n := width)).surjective previous
    have flatLt : bit.val + width * coordinate.val <
        last.val + width * pivot.val := by
      simpa [witness, finProdFinEquiv] using previousLt
    change bit.val + width * coordinate.val <
      (width - 1) + width * pivot.val at flatLt
    by_cases coordinateBefore : coordinate < pivot
    · simp [normalizedVectorRankBits, projectiveRankSentinel,
        coordinateBefore]
    · have coordinateEq : coordinate = pivot := by
        have coordinateLe : coordinate ≤ pivot := by
          apply Fin.mk_le_mk.mpr
          calc
            coordinate.val =
                (bit.val + width * coordinate.val) / width := by
              rw [Nat.add_mul_div_left _ _ widthPositive,
                Nat.div_eq_of_lt bit.isLt, zero_add]
            _ ≤ ((width - 1) + width * pivot.val) / width :=
              Nat.div_le_div_right (Nat.le_of_lt flatLt)
            _ = pivot.val := by
              rw [Nat.add_mul_div_left _ _ widthPositive,
                Nat.div_eq_of_lt (by omega), zero_add]
        exact le_antisymm coordinateLe (le_of_not_gt coordinateBefore)
      subst coordinate
      have bitBefore : bit < last := by
        apply Fin.mk_lt_mk.mpr
        omega
      have notFinal : bit.val + 1 ≠ width := by
        simp only [last] at bitBefore
        omega
      simp [normalizedVectorRankBits, projectiveRankSentinel,
        unsignedOneBits, notFinal]
  · have final : width - 1 + 1 = width := by omega
    simp [witness, normalizedVectorRankBits, projectiveRankSentinel,
      unsignedOneBits, last, final]

/-- Any rank below the sentinel has a first non-one block, and that block is
the all-zero pivot block.  All preceding blocks are unsigned one. -/
theorem rank_lt_sentinel_has_zero_pivot
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (rankLt : toLex rank < toLex (projectiveRankSentinel dimension width)) :
    ∃ pivot : Fin dimension,
      projectiveRankBlock rank pivot = (fun _ => false) ∧
        ∀ previous, previous < pivot ->
          projectiveRankBlock rank previous = unsignedOneBits width := by
  change Pi.Lex (fun left right : Fin (dimension * width) => left < right)
    (fun left right : Bool => left < right)
    rank (projectiveRankSentinel dimension width) at rankLt
  obtain ⟨witness, equalBefore, lessAt⟩ := rankLt
  obtain ⟨⟨pivot, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := dimension) (n := width)).surjective witness
  have bitFinal : bit.val + 1 = width := by
    by_contra notFinal
    have impossible : rank (finProdFinEquiv (pivot, bit)) < false := by
      simpa [projectiveRankSentinel, unsignedOneBits, notFinal] using lessAt
    exact (not_lt_of_ge (bot_le :
      false ≤ rank (finProdFinEquiv (pivot, bit)))) impossible
  have rankAtPivotFinal :
      rank (finProdFinEquiv (pivot, bit)) = false := by
    cases valueEquality : rank (finProdFinEquiv (pivot, bit)) with
    | false => rfl
    | true =>
        simp [projectiveRankSentinel, unsignedOneBits, bitFinal,
          valueEquality] at lessAt
  refine ⟨pivot, ?_, ?_⟩
  · funext selectedBit
    by_cases selectedFinal : selectedBit = bit
    · subst selectedBit
      exact rankAtPivotFinal
    · have selectedBefore : selectedBit < bit := by
        apply Fin.mk_lt_mk.mpr
        omega
      have flatBefore :
          finProdFinEquiv (pivot, selectedBit) <
            finProdFinEquiv (pivot, bit) := by
        simp [finProdFinEquiv]
        omega
      have equal := equalBefore _ flatBefore
      change rank (finProdFinEquiv (pivot, selectedBit)) = false
      rw [equal]
      have notFinal : selectedBit.val + 1 ≠ width := by omega
      simp [projectiveRankSentinel, unsignedOneBits, notFinal]
  · intro previous previousBefore
    funext selectedBit
    have coordinateBoundary :
        width * (previous.val + 1) ≤ width * pivot.val := by
      exact Nat.mul_le_mul_left width (by omega)
    have flatBefore :
        finProdFinEquiv (previous, selectedBit) <
          finProdFinEquiv (pivot, bit) := by
      apply Fin.mk_lt_mk.mpr
      change selectedBit.val + width * previous.val <
        bit.val + width * pivot.val
      calc
        selectedBit.val + width * previous.val <
            width + width * previous.val :=
          Nat.add_lt_add_right selectedBit.isLt _
        _ = width * (previous.val + 1) := by
          rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ width * pivot.val := coordinateBoundary
        _ ≤ bit.val + width * pivot.val := by omega
    have equal := equalBefore _ flatBefore
    change rank (finProdFinEquiv (previous, selectedBit)) =
      unsignedOneBits width selectedBit
    simpa [projectiveRankSentinel] using equal

theorem firstNonOneRankBlock_of_lt_sentinel
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (rankLt : toLex rank < toLex (projectiveRankSentinel dimension width)) :
    ∃ pivot : Fin dimension,
      firstNonOneRankBlock rank = some pivot ∧
        projectiveRankBlock rank pivot = (fun _ => false) := by
  obtain ⟨pivot, pivotZero, previousOne⟩ :=
    rank_lt_sentinel_has_zero_pivot widthPositive rank rankLt
  refine ⟨pivot, ?_, pivotZero⟩
  apply (firstNonOneRankBlock_eq_some_iff rank pivot).mpr
  exact ⟨pivotZero.trans_ne (falseBits_ne_unsignedOneBits widthPositive),
    previousOne⟩

/-- Field vector decoded from the semantic projective unranker. -/
noncomputable def projectiveUnrankVector
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool) :
    Fin dimension -> BinaryExtension width :=
  binaryExtensionVectorCoordinate widthPositive
    (projectiveUnrankPackedBits widthPositive rank)

@[simp] theorem projectiveUnrankVector_before
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (pivot previous : Fin dimension)
    (pivotEquality : firstNonOneRankBlock rank = some pivot)
    (previousBefore : previous < pivot) :
    projectiveUnrankVector widthPositive rank previous = 0 := by
  unfold projectiveUnrankVector binaryExtensionVectorCoordinate
  unfold projectiveUnrankPackedBits
  rw [pivotEquality]
  simp only [Equiv.symm_apply_apply]
  rw [show (fun bit =>
      (if previous < pivot then false
        else if previous = pivot then
          decodeBinaryExtension widthPositive
            (1 : BinaryExtension width) bit
        else rank (finProdFinEquiv (previous, bit)))) =
      (fun _ => false) by
    funext bit
    simp [previousBefore]]
  exact encodeBinaryExtension_zero widthPositive

@[simp] theorem projectiveUnrankVector_pivot
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension)
    (pivotEquality : firstNonOneRankBlock rank = some pivot) :
    projectiveUnrankVector widthPositive rank pivot = 1 := by
  unfold projectiveUnrankVector binaryExtensionVectorCoordinate
  unfold projectiveUnrankPackedBits
  rw [pivotEquality]
  simp only [Equiv.symm_apply_apply]
  simp

theorem firstNonzeroCoordinate_projectiveUnrankVector
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension)
    (pivotEquality : firstNonOneRankBlock rank = some pivot) :
    firstNonzeroCoordinate (projectiveUnrankVector widthPositive rank) =
      some pivot := by
  apply (firstNonzeroCoordinate_eq_some_iff _ pivot).mpr
  refine ⟨?_, ?_⟩
  · rw [projectiveUnrankVector_pivot widthPositive rank pivot pivotEquality]
    exact one_ne_zero
  · intro previous previousBefore
    exact projectiveUnrankVector_before widthPositive rank pivot previous
      pivotEquality previousBefore

theorem normalize_projectiveUnrankVector
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension)
    (pivotEquality : firstNonOneRankBlock rank = some pivot) :
    normalizeBinaryExtensionVector (projectiveUnrankVector widthPositive rank) =
      projectiveUnrankVector widthPositive rank := by
  rw [normalizeBinaryExtensionVector_eq_of_firstNonzeroCoordinate _ pivot
    (firstNonzeroCoordinate_projectiveUnrankVector widthPositive rank pivot
      pivotEquality)]
  rw [projectiveUnrankVector_pivot widthPositive rank pivot pivotEquality,
    inv_one]
  simp

theorem projectiveUnrankPackedBits_eq_vectorBits
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool) :
    projectiveUnrankPackedBits widthPositive rank =
      binaryExtensionVectorBits widthPositive
        (projectiveUnrankVector widthPositive rank) := by
  exact (binaryExtensionVectorBits_vectorCoordinate widthPositive
    (projectiveUnrankPackedBits widthPositive rank)).symm

theorem normalizedVectorRankBits_projectiveUnrankVector
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension)
    (pivotEquality : firstNonOneRankBlock rank = some pivot)
    (pivotZero : projectiveRankBlock rank pivot = (fun _ => false)) :
    normalizedVectorRankBits widthPositive
        (projectiveUnrankVector widthPositive rank) pivot = rank := by
  have previousOne :=
    (firstNonOneRankBlock_eq_some_iff rank pivot).mp pivotEquality |>.2
  funext output
  obtain ⟨⟨coordinate, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := dimension) (n := width)).surjective output
  by_cases before : coordinate < pivot
  · have atBit := congrFun (previousOne coordinate before) bit
    simpa [normalizedVectorRankBits, projectiveRankBlock, before] using
      atBit.symm
  · by_cases atPivot : coordinate = pivot
    · subst coordinate
      have atBit := congrFun pivotZero bit
      simpa [normalizedVectorRankBits, projectiveRankBlock] using atBit.symm
    · unfold normalizedVectorRankBits
      simp only [Equiv.symm_apply_apply]
      rw [ite_eq_right before, ite_eq_right atPivot]
      unfold projectiveUnrankVector binaryExtensionVectorCoordinate
      rw [decodeBinaryExtension_encode]
      unfold projectiveUnrankPackedBits
      rw [pivotEquality]
      simp [before, atPivot]

/-- Ranking after semantic unranking is the identity on the valid initial
interval. -/
theorem projectiveRankPackedBits_unrank_of_lt_sentinel
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (rankLt : toLex rank < toLex (projectiveRankSentinel dimension width)) :
    projectiveRankPackedBits
        (projectiveUnrankPackedBits widthPositive rank) = rank := by
  obtain ⟨pivot, pivotEquality, pivotZero⟩ :=
    firstNonOneRankBlock_of_lt_sentinel widthPositive rank rankLt
  rw [projectiveUnrankPackedBits_eq_vectorBits]
  rw [projectiveRankPackedBits_vectorBits widthPositive
    (projectiveUnrankVector widthPositive rank) pivot
    (firstNonzeroCoordinate_projectiveUnrankVector widthPositive rank pivot
      pivotEquality)]
  exact normalizedVectorRankBits_projectiveUnrankVector widthPositive rank
    pivot pivotEquality pivotZero

theorem projectiveDirectionRankBits_lt_sentinel
    (widthPositive : 0 < width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    toLex (projectiveDirectionRankBits widthPositive direction) <
      toLex (projectiveRankSentinel dimension width) := by
  classical
  let vector := normalizeBinaryExtensionVector direction.rep
  have vectorNonzero : vector ≠ 0 :=
    normalizeBinaryExtensionVector_ne_zero direction.rep
      direction.rep_nonzero
  have existsNonzero : ∃ coordinate, vector coordinate ≠ 0 := by
    by_contra noneNonzero
    apply vectorNonzero
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp noneNonzero coordinate)
  let pivot :=
    Fin.find (fun coordinate => vector coordinate ≠ 0) existsNonzero
  have pivotEquality : firstNonzeroCoordinate vector = some pivot := by
    simp [firstNonzeroCoordinate, existsNonzero, pivot]
  unfold projectiveDirectionRankBits projectiveDirectionKey
  rw [projectiveRankPackedBits_vectorBits widthPositive vector pivot
    pivotEquality]
  exact normalizedVectorRankBits_lt_sentinel widthPositive vector pivot

theorem exists_projectiveDirectionRankBits_eq_of_lt_sentinel
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (rankLt : toLex rank < toLex (projectiveRankSentinel dimension width)) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      projectiveDirectionRankBits widthPositive direction = rank := by
  obtain ⟨pivot, pivotEquality, _⟩ :=
    firstNonOneRankBlock_of_lt_sentinel widthPositive rank rankLt
  let vector := projectiveUnrankVector widthPositive rank
  have vectorAtPivot : vector pivot = 1 :=
    projectiveUnrankVector_pivot widthPositive rank pivot pivotEquality
  have vectorNonzero : vector ≠ 0 := by
    intro vectorZero
    have atPivot := congrFun vectorZero pivot
    rw [vectorAtPivot] at atPivot
    exact one_ne_zero atPivot
  refine ⟨Projectivization.mk (BinaryExtension width)
    vector vectorNonzero, ?_⟩
  unfold projectiveDirectionRankBits
  rw [projectiveDirectionKey_mk widthPositive vector vectorNonzero]
  rw [normalize_projectiveUnrankVector widthPositive rank pivot
    pivotEquality]
  rw [← projectiveUnrankPackedBits_eq_vectorBits widthPositive rank]
  exact projectiveRankPackedBits_unrank_of_lt_sentinel
    widthPositive rank rankLt

/-- The projective direction represented by a packed rank below the
sentinel. -/
noncomputable def projectiveDirectionOfRank
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (rankLt : toLex rank < toLex (projectiveRankSentinel dimension width)) :
    ℙ (BinaryExtension width) (Fin dimension -> BinaryExtension width) :=
  Classical.choose
    (exists_projectiveDirectionRankBits_eq_of_lt_sentinel
      widthPositive rank rankLt)

@[simp] theorem projectiveDirectionRankBits_directionOfRank
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (rankLt : toLex rank < toLex (projectiveRankSentinel dimension width)) :
    projectiveDirectionRankBits widthPositive
        (projectiveDirectionOfRank widthPositive rank rankLt) = rank :=
  Classical.choose_spec
    (exists_projectiveDirectionRankBits_eq_of_lt_sentinel
      widthPositive rank rankLt)

/-- Packed projective ranks are exactly the strict initial lexicographic
interval below the all-one-digit sentinel. -/
noncomputable def projectiveDirectionRankEquivIio
    (widthPositive : 0 < width) :
    ℙ (BinaryExtension width) (Fin dimension -> BinaryExtension width) ≃
      {rank : Lex (Fin (dimension * width) -> Bool) //
        rank < toLex (projectiveRankSentinel dimension width)} where
  toFun direction :=
    ⟨toLex (projectiveDirectionRankBits widthPositive direction),
      projectiveDirectionRankBits_lt_sentinel widthPositive direction⟩
  invFun rank :=
    projectiveDirectionOfRank widthPositive (ofLex rank.1) (by
      simpa only [toLex_ofLex] using rank.2)
  left_inv direction := by
    apply projectiveDirectionRankBits_injective widthPositive
    exact projectiveDirectionRankBits_directionOfRank widthPositive
      (projectiveDirectionRankBits widthPositive direction)
      (projectiveDirectionRankBits_lt_sentinel widthPositive direction)
  right_inv rank := by
    apply Subtype.ext
    apply toLex_inj.mpr
    exact projectiveDirectionRankBits_directionOfRank widthPositive
      (ofLex rank.1) (by simpa only [toLex_ofLex] using rank.2)

theorem card_projectiveRankInterval
    (widthPositive : 0 < width) :
    Nat.card {rank : Lex (Fin (dimension * width) -> Bool) //
        rank < toLex (projectiveRankSentinel dimension width)} =
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := by
  exact Nat.card_congr (projectiveDirectionRankEquivIio widthPositive).symm

/-- Test a selected input bit against one hardwired rank bit. -/
def rankBitEqualsConstantExpression
    (expected : Bool)
    (input : Fin n) : DeMorgan.Expression n :=
  if expected then .input input else .not (.input input)

@[simp] theorem rankBitEqualsConstantExpression_eval_eq_true_iff
    (expected : Bool)
    (index : Fin n)
    (input : Fin n -> Bool) :
    (rankBitEqualsConstantExpression expected index).eval input = true ↔
      input index = expected := by
  cases expected <;> cases valueEquality : input index <;>
    simp [rankBitEqualsConstantExpression, DeMorgan.Expression.eval,
      valueEquality]

theorem rankBitEqualsConstantExpression_standardCost_le
    (expected : Bool)
    (index : Fin n) :
    (rankBitEqualsConstantExpression expected index).standardCost <= 1 := by
  cases expected <;>
    simp [rankBitEqualsConstantExpression,
      DeMorgan.Expression.standardCost]

/-- Equality of one rank block with the big-endian unsigned digit one. -/
def rankBlockOneExpression
    (dimension width : Nat)
    (coordinate : Fin dimension) :
    DeMorgan.Expression (dimension * width) :=
  DeMorgan.Expression.finAnd width fun bit =>
    rankBitEqualsConstantExpression (unsignedOneBits width bit)
      (finProdFinEquiv (coordinate, bit))

/-- Boolean flag computed by `rankBlockOneExpression`. -/
def rankBlockOneFlag
    (rank : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) : Bool :=
  (rankBlockOneExpression dimension width coordinate).eval rank

theorem rankBlockOneFlag_eq_true_iff
    (rank : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) :
    rankBlockOneFlag rank coordinate = true ↔
      projectiveRankBlock rank coordinate = unsignedOneBits width := by
  unfold rankBlockOneFlag rankBlockOneExpression
  rw [DeMorgan.Expression.finAnd_eval,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · intro allBits
    funext bit
    exact (rankBitEqualsConstantExpression_eval_eq_true_iff
      _ _ rank).mp (allBits bit)
  · intro equalBlocks bit
    apply (rankBitEqualsConstantExpression_eval_eq_true_iff
      _ _ rank).mpr
    exact congrFun equalBlocks bit

theorem rankBlockOneFlag_eq_false_iff
    (rank : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) :
    rankBlockOneFlag rank coordinate = false ↔
      projectiveRankBlock rank coordinate ≠ unsignedOneBits width := by
  constructor
  · intro flagFalse blocksEqual
    have flagTrue :=
      (rankBlockOneFlag_eq_true_iff rank coordinate).mpr blocksEqual
    rw [flagFalse] at flagTrue
    contradiction
  · intro blocksDifferent
    cases flagEquality : rankBlockOneFlag rank coordinate with
    | false => rfl
    | true =>
        exact False.elim (blocksDifferent
          ((rankBlockOneFlag_eq_true_iff rank coordinate).mp flagEquality))

/-- One-hot flag for the first rank block that is not unsigned one. -/
def firstNonOneRankExpression
    (dimension width : Nat)
    (pivot : Fin dimension) :
    DeMorgan.Expression (dimension * width) :=
  .and (.not (rankBlockOneExpression dimension width pivot))
    (DeMorgan.Expression.finAnd dimension fun previous =>
      if previous < pivot then
        rankBlockOneExpression dimension width previous
      else .constant true)

@[simp] theorem firstNonOneRankExpression_eval
    (rank : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension) :
    (firstNonOneRankExpression dimension width pivot).eval rank =
      (!(rankBlockOneFlag rank pivot) &&
        DeMorgan.Expression.finAndValue dimension fun previous =>
          if previous < pivot then rankBlockOneFlag rank previous
          else true) := by
  rw [firstNonOneRankExpression, DeMorgan.Expression.eval,
    DeMorgan.Expression.finAnd_eval]
  congr 1
  apply congrArg
  funext previous
  split_ifs <;> rfl

theorem firstNonOneRankExpression_eval_eq_true_iff
    (rank : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension) :
    (firstNonOneRankExpression dimension width pivot).eval rank = true ↔
      firstNonOneRankBlock rank = some pivot := by
  rw [firstNonOneRankExpression_eval, Bool.and_eq_true,
    Bool.not_eq_true',
    DeMorgan.Expression.finAndValue_eq_true_iff,
    firstNonOneRankBlock_eq_some_iff,
    rankBlockOneFlag_eq_false_iff]
  constructor
  · rintro ⟨pivotDifferent, previousFlags⟩
    exact ⟨pivotDifferent, fun previous previousBefore =>
      (rankBlockOneFlag_eq_true_iff rank previous).mp
        (by simpa [previousBefore] using previousFlags previous)⟩
  · rintro ⟨pivotDifferent, previousBlocks⟩
    refine ⟨pivotDifferent, ?_⟩
    intro previous
    split_ifs with previousBefore
    · exact (rankBlockOneFlag_eq_true_iff rank previous).mpr
        (previousBlocks previous previousBefore)
    · rfl

/-- One output value selected by a candidate unrank pivot. -/
noncomputable def unrankValueExpression
    (widthPositive : 0 < width)
    (coordinate : Fin dimension)
    (bit : Fin width)
    (pivot : Fin dimension) :
    DeMorgan.Expression (dimension * width) :=
  if coordinate < pivot then .constant false
  else if coordinate = pivot then
    .constant (decodeBinaryExtension widthPositive
      (1 : BinaryExtension width) bit)
  else .input (finProdFinEquiv (coordinate, bit))

/-- One output bit of the projective unrank circuit. -/
noncomputable def projectiveUnrankBitExpression
    (dimension : Nat)
    (widthPositive : 0 < width)
    (output : Fin (dimension * width)) :
    DeMorgan.Expression (dimension * width) :=
  let coordinateAndBit :=
    (finProdFinEquiv (m := dimension) (n := width)).symm output
  DeMorgan.Expression.finOr dimension fun pivot =>
    .and (firstNonOneRankExpression dimension width pivot)
      (unrankValueExpression widthPositive coordinateAndBit.1
        coordinateAndBit.2 pivot)

theorem projectiveUnrankBitExpression_eval
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool)
    (output : Fin (dimension * width)) :
    (projectiveUnrankBitExpression dimension widthPositive output).eval rank =
      projectiveUnrankPackedBits widthPositive rank output := by
  unfold projectiveUnrankBitExpression
  rw [DeMorgan.Expression.finOr_eval]
  let coordinateAndBit :=
    (finProdFinEquiv (m := dimension) (n := width)).symm output
  change DeMorgan.Expression.finOrValue dimension (fun pivot =>
      (firstNonOneRankExpression dimension width pivot).eval rank &&
        (unrankValueExpression widthPositive coordinateAndBit.1
          coordinateAndBit.2 pivot).eval rank) = _
  generalize firstEquality : firstNonOneRankBlock rank = first
  cases first with
  | none =>
      have noSelected : ∀ pivot : Fin dimension,
          (firstNonOneRankExpression dimension width pivot).eval rank ≠
            true := by
        intro pivot selectedTrue
        have selectedEquality :=
          (firstNonOneRankExpression_eval_eq_true_iff rank pivot).mp
            selectedTrue
        rw [firstEquality] at selectedEquality
        cases selectedEquality
      have foldedFalse :
          DeMorgan.Expression.finOrValue dimension (fun pivot =>
            (firstNonOneRankExpression dimension width pivot).eval rank &&
              (unrankValueExpression widthPositive coordinateAndBit.1
                coordinateAndBit.2 pivot).eval rank) = false := by
        apply Bool.eq_false_iff.mpr
        intro foldedTrue
        obtain ⟨pivot, termTrue⟩ :=
          (DeMorgan.Expression.finOrValue_eq_true_iff _ _).mp foldedTrue
        rw [Bool.and_eq_true] at termTrue
        exact noSelected pivot termTrue.1
      rw [foldedFalse]
      unfold projectiveUnrankPackedBits
      rw [firstEquality]
  | some pivot =>
      rw [DeMorgan.Expression.finOrValue_oneHot dimension pivot]
      · unfold projectiveUnrankPackedBits unrankValueExpression
        rw [firstEquality]
        dsimp only [coordinateAndBit]
        split_ifs
        · rfl
        · rfl
        · change rank
            (finProdFinEquiv
              ((finProdFinEquiv
                (m := dimension) (n := width)).symm output)) = rank output
          rw [Equiv.apply_symm_apply]
      · exact (firstNonOneRankExpression_eval_eq_true_iff rank pivot).mpr
          firstEquality
      · intro selected selectedTrue
        have selectedEquality :=
          (firstNonOneRankExpression_eval_eq_true_iff rank selected).mp
            selectedTrue
        exact Option.some.inj (selectedEquality.symm.trans firstEquality)

/-- Gate count of one independently compiled unrank output. -/
@[reducible] noncomputable def projectiveUnrankBitGateCount
    (dimension : Nat)
    (widthPositive : 0 < width)
    (output : Fin (dimension * width)) : Nat :=
  (projectiveUnrankBitExpression dimension widthPositive output).gateCount

/-- Explicit circuit reconstructing the canonical normalized vector from a
valid packed projective rank. -/
noncomputable def projectiveUnrankPackedCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :
    Circuit DeMorgan.signature (dimension * width)
      (dimension * width) :=
  Circuit.parallelFin (dimension * width) fun output =>
      (projectiveUnrankBitExpression dimension widthPositive output).circuit

@[simp] theorem projectiveUnrankPackedCircuit_size
    (dimension : Nat)
    (widthPositive : 0 < width) :
    (projectiveUnrankPackedCircuit dimension widthPositive).size =
      ∑ output, projectiveUnrankBitGateCount dimension widthPositive output := by
  simp [projectiveUnrankPackedCircuit, projectiveUnrankBitGateCount]

@[simp] theorem projectiveUnrankPackedCircuit_eval
    (widthPositive : 0 < width)
    (rank : Fin (dimension * width) -> Bool) :
    (projectiveUnrankPackedCircuit dimension widthPositive).eval
        DeMorgan.interpretation rank =
      projectiveUnrankPackedBits widthPositive rank := by
  funext output
  rw [projectiveUnrankPackedCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval,
    projectiveUnrankBitExpression_eval]

/-- Circuit-level rank/unrank correctness on every projective direction. -/
theorem projectiveUnrankPackedCircuit_eval_directionRank
    (widthPositive : 0 < width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    (projectiveUnrankPackedCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (projectiveDirectionRankBits widthPositive direction) =
      projectiveDirectionKey widthPositive direction := by
  rw [projectiveUnrankPackedCircuit_eval,
    projectiveUnrankPackedBits_directionRank]

theorem rankBlockOneExpression_standardCost_le
    (coordinate : Fin dimension) :
    (rankBlockOneExpression dimension width coordinate).standardCost <=
      2 * width := by
  rw [rankBlockOneExpression,
    DeMorgan.Expression.finAnd_standardCost]
  have bitBound :
      (∑ bit : Fin width,
        (rankBitEqualsConstantExpression (unsignedOneBits width bit)
          (finProdFinEquiv (coordinate, bit))).standardCost) <=
      ∑ _bit : Fin width, 1 := by
    exact Finset.sum_le_sum fun bit _ =>
      rankBitEqualsConstantExpression_standardCost_le _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, Nat.mul_one] at bitBound
  omega

theorem firstNonOneRankExpression_standardCost_le
    (pivot : Fin dimension) :
    (firstNonOneRankExpression dimension width pivot).standardCost <=
      2 * width + 2 + dimension * (2 * width + 1) := by
  rw [firstNonOneRankExpression,
    DeMorgan.Expression.standardCost,
    DeMorgan.Expression.finAnd_standardCost]
  have previousBound :
      (∑ previous : Fin dimension,
        (if previous < pivot then
          rankBlockOneExpression dimension width previous
        else DeMorgan.Expression.constant true).standardCost) <=
      ∑ _previous : Fin dimension, (2 * width) := by
    apply Finset.sum_le_sum
    intro previous _
    split_ifs
    · exact rankBlockOneExpression_standardCost_le previous
    · simp [DeMorgan.Expression.standardCost]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] at previousBound
  have pivotBound :=
    rankBlockOneExpression_standardCost_le
      (dimension := dimension) (width := width) pivot
  calc
    ((rankBlockOneExpression dimension width pivot).standardCost + 1) +
        ((∑ previous : Fin dimension,
          (if previous < pivot then
            rankBlockOneExpression dimension width previous
          else DeMorgan.Expression.constant true).standardCost) +
          dimension) + 1 <=
      (2 * width + 1) +
        (dimension * (2 * width) + dimension) + 1 := by omega
    _ = 2 * width + 2 + dimension * (2 * width + 1) := by ring

theorem projectiveUnrankBitExpression_standardCost_le
    (widthPositive : 0 < width)
    (output : Fin (dimension * width)) :
    (projectiveUnrankBitExpression dimension widthPositive output).standardCost <=
      dimension *
        (2 * width + 2 + dimension * (2 * width + 1) + 2) := by
  unfold projectiveUnrankBitExpression
  rw [DeMorgan.Expression.finOr_standardCost]
  have termBound : ∀ pivot : Fin dimension,
      ((firstNonOneRankExpression dimension width pivot).and
        (unrankValueExpression widthPositive
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).1
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).2
          pivot)).standardCost <=
        2 * width + 2 + dimension * (2 * width + 1) + 1 := by
    intro pivot
    simp only [DeMorgan.Expression.standardCost]
    have flagBound := firstNonOneRankExpression_standardCost_le
      (width := width) pivot
    have valueZero :
        (unrankValueExpression widthPositive
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).1
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).2
          pivot).standardCost = 0 := by
      unfold unrankValueExpression
      split_ifs <;> rfl
    rw [valueZero]
    omega
  calc
    (∑ pivot : Fin dimension,
        ((firstNonOneRankExpression dimension width pivot).and
          (unrankValueExpression widthPositive
            ((finProdFinEquiv
              (m := dimension) (n := width)).symm output).1
            ((finProdFinEquiv
              (m := dimension) (n := width)).symm output).2
            pivot)).standardCost) + dimension <=
      (∑ _pivot : Fin dimension,
        (2 * width + 2 + dimension * (2 * width + 1) + 1)) +
          dimension := by
      exact Nat.add_le_add_right
        (Finset.sum_le_sum fun pivot _ => termBound pivot) dimension
    _ = dimension *
        (2 * width + 2 + dimension * (2 * width + 1) + 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      ring

/-- Polynomial gate ledger for projective unranking. -/
theorem projectiveUnrankPackedCircuit_cost_le
    (widthPositive : 0 < width) :
    (projectiveUnrankPackedCircuit dimension widthPositive).cost
        DeMorgan.standardCost <=
      (dimension * width) *
        (dimension *
          (2 * width + 2 + dimension * (2 * width + 1) + 2)) := by
  rw [projectiveUnrankPackedCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    ∑ output : Fin (dimension * width),
        (projectiveUnrankBitExpression dimension widthPositive output).standardCost <=
      ∑ _output : Fin (dimension * width),
        (dimension *
          (2 * width + 2 + dimension * (2 * width + 1) + 2)) := by
      exact Finset.sum_le_sum fun output _ =>
        projectiveUnrankBitExpression_standardCost_le widthPositive output
    _ = (dimension * width) *
        (dimension *
          (2 * width + 2 + dimension * (2 * width + 1) + 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]

/-- Gate count of the independently compiled rank outputs. -/
@[reducible] def projectiveRankBitGateCount
    (dimension width : Nat)
    (output : Fin (dimension * width)) : Nat :=
  (projectiveRankBitExpression dimension width output).gateCount

/-- Explicit circuit converting a normalized nonzero vector to its block
rank. -/
def projectiveRankPackedCircuit (dimension width : Nat) :
    Circuit DeMorgan.signature (dimension * width)
      (dimension * width) :=
  Circuit.parallelFin (dimension * width) fun output =>
      (projectiveRankBitExpression dimension width output).circuit

@[simp] theorem projectiveRankPackedCircuit_size (dimension width : Nat) :
    (projectiveRankPackedCircuit dimension width).size =
      ∑ output, projectiveRankBitGateCount dimension width output := by
  simp [projectiveRankPackedCircuit, projectiveRankBitGateCount]

@[simp] theorem projectiveRankPackedCircuit_eval
    (input : Fin (dimension * width) -> Bool) :
    (projectiveRankPackedCircuit dimension width).eval
        DeMorgan.interpretation input =
      projectiveRankPackedBits input := by
  funext output
  rw [projectiveRankPackedCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  rfl

/-- Normalize a projective representative and then emit its block rank. -/
noncomputable def projectiveDirectionRankCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :=
  (projectiveRankPackedCircuit dimension width).comp
    (normalizeBinaryExtensionVectorCircuit dimension widthPositive)

@[simp] theorem projectiveDirectionRankCircuit_eval_projective
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    (projectiveDirectionRankCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (binaryExtensionVectorBits widthPositive direction.rep) =
      projectiveDirectionRankBits widthPositive direction := by
  rw [projectiveDirectionRankCircuit, Circuit.eval_comp,
    normalizeBinaryExtensionVectorCircuit_eval_projective
      widthPositive widthAtLeastTwo direction,
    projectiveRankPackedCircuit_eval]
  rfl

theorem firstNonzeroDirectExpression_standardCost_le
    (pivot : Fin dimension) :
    (firstNonzeroDirectExpression dimension width pivot).standardCost <=
      width + 1 + dimension * (width + 2) := by
  rw [firstNonzeroDirectExpression,
    DeMorgan.Expression.standardCost,
    vectorCoordinateNonzeroExpression_standardCost,
    DeMorgan.Expression.finAnd_standardCost]
  have termsBound :
      (∑ previous : Fin dimension,
        (if previous < pivot then
          (vectorCoordinateNonzeroExpression dimension width previous).not
        else DeMorgan.Expression.constant true).standardCost) <=
      ∑ _previous : Fin dimension, (width + 1) := by
    apply Finset.sum_le_sum
    intro previous _
    split_ifs <;>
      simp [DeMorgan.Expression.standardCost,
        vectorCoordinateNonzeroExpression_standardCost]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] at termsBound
  calc
    width +
        ((∑ previous : Fin dimension,
          (if previous < pivot then
            (vectorCoordinateNonzeroExpression dimension width previous).not
          else DeMorgan.Expression.constant true).standardCost) +
          dimension) + 1 <=
      width + (dimension * (width + 1) + dimension) + 1 := by
        omega
    _ = width + 1 + dimension * (width + 2) := by ring

theorem projectiveRankBitExpression_standardCost_le
    (output : Fin (dimension * width)) :
    (projectiveRankBitExpression dimension width output).standardCost <=
      dimension * (width + 1 + dimension * (width + 2) + 2) := by
  unfold projectiveRankBitExpression
  rw [DeMorgan.Expression.finOr_standardCost]
  have termBound : ∀ pivot : Fin dimension,
      ((firstNonzeroDirectExpression dimension width pivot).and
        (rankValueExpression dimension width
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).1
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).2
          pivot)).standardCost <=
        width + 1 + dimension * (width + 2) + 1 := by
    intro pivot
    simp only [DeMorgan.Expression.standardCost]
    have flagBound := firstNonzeroDirectExpression_standardCost_le
      (width := width) pivot
    have valueZero :
        (rankValueExpression dimension width
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).1
          ((finProdFinEquiv
            (m := dimension) (n := width)).symm output).2
          pivot).standardCost = 0 := by
      unfold rankValueExpression
      split_ifs <;> rfl
    rw [valueZero]
    omega
  calc
    (∑ pivot : Fin dimension,
        ((firstNonzeroDirectExpression dimension width pivot).and
          (rankValueExpression dimension width
            ((finProdFinEquiv
              (m := dimension) (n := width)).symm output).1
            ((finProdFinEquiv
              (m := dimension) (n := width)).symm output).2
            pivot)).standardCost) + dimension <=
        (∑ _pivot : Fin dimension,
          (width + 1 + dimension * (width + 2) + 1)) + dimension := by
      exact Nat.add_le_add_right
        (Finset.sum_le_sum fun pivot _ => termBound pivot) dimension
    _ = dimension * (width + 1 + dimension * (width + 2) + 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      ring

/-- Polynomial gate ledger for the packed rank transformation. -/
theorem projectiveRankPackedCircuit_cost_le :
    (projectiveRankPackedCircuit dimension width).cost
        DeMorgan.standardCost <=
      (dimension * width) *
        (dimension * (width + 1 + dimension * (width + 2) + 2)) := by
  rw [projectiveRankPackedCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    ∑ output : Fin (dimension * width),
        (projectiveRankBitExpression dimension width output).standardCost <=
      ∑ _output : Fin (dimension * width),
        (dimension * (width + 1 + dimension * (width + 2) + 2)) := by
      exact Finset.sum_le_sum fun output _ =>
        projectiveRankBitExpression_standardCost_le output
    _ = (dimension * width) *
        (dimension * (width + 1 + dimension * (width + 2) + 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]

/-- The complete normalizer-plus-ranker remains polynomial in the extension
width for fixed projective dimension. -/
theorem projectiveDirectionRankCircuit_cost_le
    (widthPositive : 0 < width) :
    (projectiveDirectionRankCircuit dimension widthPositive).cost
        DeMorgan.standardCost <=
      projectiveNormalizationCircuitBound dimension width +
        (dimension * width) *
          (dimension * (width + 1 + dimension * (width + 2) + 2)) := by
  rw [projectiveDirectionRankCircuit, Circuit.cost_comp]
  exact Nat.add_le_add
    (normalizeBinaryExtensionVectorCircuit_cost_le widthPositive)
    projectiveRankPackedCircuit_cost_le

end MassProduction
end Algebraic
