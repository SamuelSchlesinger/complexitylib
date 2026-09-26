/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Expression
public import Complexitylib.Algebraic.MassProduction.Projective

/-!
# Polynomial-size projective normalization circuits

This file realizes first-nonzero projective normalization as an explicit
shared De Morgan circuit.  It first computes one nonzero flag per field
coordinate, selects the first nonzero coordinate once, applies the shared
binary-field inverse circuit once, and then multiplies every coordinate by
that inverse in parallel.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators
open scoped LinearAlgebra.Projectivization

/-- Direct `OR` expression testing whether one packed field coordinate has a
true bit. -/
def vectorCoordinateNonzeroExpression
    (dimension width : Nat)
    (coordinate : Fin dimension) :
    DeMorgan.Expression (dimension * width) :=
  DeMorgan.Expression.finOr width fun bit =>
    .input (finProdFinEquiv (coordinate, bit))

/-- Semantic nonzero flags for every coordinate of a packed field vector. -/
def vectorCoordinateNonzeroFlags
    (input : Fin (dimension * width) -> Bool) : Fin dimension -> Bool :=
  fun coordinate =>
    DeMorgan.Expression.finOrValue width fun bit =>
      input (finProdFinEquiv (coordinate, bit))

@[simp] theorem vectorCoordinateNonzeroExpression_eval
    (coordinate : Fin dimension)
    (input : Fin (dimension * width) -> Bool) :
    (vectorCoordinateNonzeroExpression dimension width coordinate).eval
        input =
      vectorCoordinateNonzeroFlags input coordinate := by
  rw [vectorCoordinateNonzeroExpression,
    DeMorgan.Expression.finOr_eval]
  rfl

theorem vectorCoordinateNonzeroFlags_eq_true_iff
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) :
    vectorCoordinateNonzeroFlags input coordinate = true ↔
      binaryExtensionVectorCoordinate widthPositive input coordinate ≠ 0 := by
  unfold vectorCoordinateNonzeroFlags binaryExtensionVectorCoordinate
  rw [DeMorgan.Expression.finOrValue_eq_true_iff,
    encodeBinaryExtension_ne_zero_iff]

@[simp] theorem vectorCoordinateNonzeroExpression_standardCost
    (coordinate : Fin dimension) :
    (vectorCoordinateNonzeroExpression dimension width coordinate).standardCost =
      width := by
  rw [vectorCoordinateNonzeroExpression,
    DeMorgan.Expression.finOr_standardCost]
  simp [DeMorgan.Expression.standardCost]

/-- Gate count of one compiled coordinate nonzero test. -/
@[reducible] def vectorCoordinateNonzeroGateCount
    (dimension width : Nat)
    (coordinate : Fin dimension) : Nat :=
  (vectorCoordinateNonzeroExpression dimension width coordinate).gateCount

/-- Compute and share all coordinate nonzero flags. -/
def vectorCoordinateNonzeroCircuit (dimension width : Nat) :
    Circuit DeMorgan.signature (dimension * width)
      dimension :=
  Circuit.parallelFin dimension fun coordinate =>
      (vectorCoordinateNonzeroExpression dimension width coordinate).circuit

@[simp] theorem vectorCoordinateNonzeroCircuit_size (dimension width : Nat) :
    (vectorCoordinateNonzeroCircuit dimension width).size =
      ∑ coordinate, vectorCoordinateNonzeroGateCount dimension width coordinate := by
  simp [vectorCoordinateNonzeroCircuit, vectorCoordinateNonzeroGateCount]

@[simp] theorem vectorCoordinateNonzeroCircuit_eval
    (input : Fin (dimension * width) -> Bool) :
    (vectorCoordinateNonzeroCircuit dimension width).eval
        DeMorgan.interpretation input =
      vectorCoordinateNonzeroFlags input := by
  funext coordinate
  rw [vectorCoordinateNonzeroCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval,
    vectorCoordinateNonzeroExpression_eval]

/-- All coordinate nonzero tests together cost exactly `dimension * width`. -/
@[simp] theorem vectorCoordinateNonzeroCircuit_cost :
    (vectorCoordinateNonzeroCircuit dimension width).cost
        DeMorgan.standardCost = dimension * width := by
  rw [vectorCoordinateNonzeroCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost,
    vectorCoordinateNonzeroExpression_standardCost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]

/-- Original packed vector followed by its shared coordinate nonzero flags. -/
def normalizationFlaggedBits
    (input : Fin (dimension * width) -> Bool) :
    Fin (dimension * width + dimension) -> Bool :=
  Fin.append input (vectorCoordinateNonzeroFlags input)

/-- Circuit retaining the original vector and appending all nonzero flags. -/
def normalizationFlaggedCircuit (dimension width : Nat) :=
  (Circuit.id DeMorgan.signature (dimension * width)).parallel
    (vectorCoordinateNonzeroCircuit dimension width)

/-- The exact gate count of `normalizationFlaggedCircuit`. -/
@[simp] theorem normalizationFlaggedCircuit_size
    (dimension width : Nat) :
    (normalizationFlaggedCircuit dimension width).size =
      ∑ coordinate : Fin dimension,
        vectorCoordinateNonzeroGateCount dimension width coordinate := by
  simp [normalizationFlaggedCircuit]

@[simp] theorem normalizationFlaggedCircuit_eval
    (input : Fin (dimension * width) -> Bool) :
    (normalizationFlaggedCircuit dimension width).eval
        DeMorgan.interpretation input =
      normalizationFlaggedBits input := by
  simp [normalizationFlaggedCircuit, normalizationFlaggedBits]

@[simp] theorem normalizationFlaggedCircuit_cost :
    (normalizationFlaggedCircuit dimension width).cost
        DeMorgan.standardCost = dimension * width := by
  simp [normalizationFlaggedCircuit]

/-- Index of an original vector bit in the flagged intermediate layout. -/
def normalizationVectorBitIndex
    (index : Fin (dimension * width)) :
    Fin (dimension * width + dimension) :=
  Fin.castAdd dimension index

/-- Index of one nonzero flag in the flagged intermediate layout. -/
def normalizationFlagIndex
    (coordinate : Fin dimension) :
    Fin (dimension * width + dimension) :=
  Fin.natAdd (dimension * width) coordinate

@[simp] theorem normalizationFlaggedBits_vectorBit
    (input : Fin (dimension * width) -> Bool)
    (index : Fin (dimension * width)) :
    normalizationFlaggedBits input (normalizationVectorBitIndex index) =
      input index := by
  simp [normalizationFlaggedBits, normalizationVectorBitIndex]

@[simp] theorem normalizationFlaggedBits_flag
    (input : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) :
    normalizationFlaggedBits input (normalizationFlagIndex coordinate) =
      vectorCoordinateNonzeroFlags input coordinate := by
  simp [normalizationFlaggedBits, normalizationFlagIndex]

/-- Whether a coordinate is the first asserted nonzero flag. -/
def firstNonzeroFlag
    (flags : Fin dimension -> Bool)
    (pivot : Fin dimension) : Bool :=
  flags pivot &&
    DeMorgan.Expression.finAndValue dimension fun previous =>
      if previous < pivot then !(flags previous) else true

/-- Expression computing one first-nonzero one-hot flag from the shared
coordinate flags. -/
def firstNonzeroFlagExpression
    (dimension width : Nat)
    (pivot : Fin dimension) :
    DeMorgan.Expression (dimension * width + dimension) :=
  .and (.input (normalizationFlagIndex pivot))
    (DeMorgan.Expression.finAnd dimension fun previous =>
      if previous < pivot then
        .not (.input (normalizationFlagIndex previous))
      else .constant true)

@[simp] theorem firstNonzeroFlagExpression_eval_flagged
    (input : Fin (dimension * width) -> Bool)
    (pivot : Fin dimension) :
    (firstNonzeroFlagExpression dimension width pivot).eval
        (normalizationFlaggedBits input) =
      firstNonzeroFlag (vectorCoordinateNonzeroFlags input) pivot := by
  rw [firstNonzeroFlagExpression, DeMorgan.Expression.eval,
    DeMorgan.Expression.finAnd_eval]
  unfold firstNonzeroFlag
  simp only [DeMorgan.Expression.eval,
    normalizationFlaggedBits_flag]
  congr 1
  apply congrArg
  funext previous
  split_ifs <;>
    simp [DeMorgan.Expression.eval, normalizationFlaggedBits_flag]

theorem firstNonzeroFlag_vectorBits_eq_true_iff
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension) :
    firstNonzeroFlag
        (vectorCoordinateNonzeroFlags
          (binaryExtensionVectorBits widthPositive vector)) pivot = true ↔
      firstNonzeroCoordinate vector = some pivot := by
  rw [firstNonzeroCoordinate_eq_some_iff]
  unfold firstNonzeroFlag
  rw [Bool.and_eq_true,
    DeMorgan.Expression.finAndValue_eq_true_iff]
  constructor
  · rintro ⟨pivotFlag, priorFlags⟩
    refine ⟨?_, ?_⟩
    · simpa only [binaryExtensionVectorCoordinate_vectorBits] using
        (vectorCoordinateNonzeroFlags_eq_true_iff widthPositive
          (binaryExtensionVectorBits widthPositive vector) pivot).mp
          pivotFlag
    · intro previous previousLt
      have priorFalse := priorFlags previous
      simp only [ite_eq_left previousLt, Bool.not_eq_true'] at priorFalse
      by_contra previousNonzero
      have priorTrue :=
        (vectorCoordinateNonzeroFlags_eq_true_iff widthPositive
          (binaryExtensionVectorBits widthPositive vector)
          previous).mpr <| by
            simpa only [binaryExtensionVectorCoordinate_vectorBits] using
              previousNonzero
      rw [priorTrue] at priorFalse
      contradiction
  · rintro ⟨pivotNonzero, previousZero⟩
    constructor
    · apply (vectorCoordinateNonzeroFlags_eq_true_iff widthPositive
        (binaryExtensionVectorBits widthPositive vector) pivot).mpr
      simpa only [binaryExtensionVectorCoordinate_vectorBits]
    · intro previous
      split_ifs with previousLt
      · rw [Bool.not_eq_true']
        apply Bool.eq_false_iff.mpr
        intro previousTrue
        have previousNonzero :=
          (vectorCoordinateNonzeroFlags_eq_true_iff widthPositive
            (binaryExtensionVectorBits widthPositive vector)
            previous).mp previousTrue
        rw [binaryExtensionVectorCoordinate_vectorBits,
          previousZero previous previousLt] at previousNonzero
        exact previousNonzero rfl
      · rfl

/-- The selected pivot bits computed from the flagged layout. -/
def normalizationPivotBits
    (input : Fin (dimension * width) -> Bool) : Fin width -> Bool :=
  fun bit =>
    DeMorgan.Expression.finOrValue dimension fun pivot =>
      firstNonzeroFlag (vectorCoordinateNonzeroFlags input) pivot &&
        input (finProdFinEquiv (pivot, bit))

/-- Expression for one bit of the selected first nonzero coordinate. -/
def normalizationPivotBitExpression
    (dimension width : Nat)
    (bit : Fin width) :
    DeMorgan.Expression (dimension * width + dimension) :=
  DeMorgan.Expression.finOr dimension fun pivot =>
    .and (firstNonzeroFlagExpression dimension width pivot)
      (.input (normalizationVectorBitIndex
        (finProdFinEquiv (pivot, bit))))

@[simp] theorem normalizationPivotBitExpression_eval_flagged
    (input : Fin (dimension * width) -> Bool)
    (bit : Fin width) :
    (normalizationPivotBitExpression dimension width bit).eval
        (normalizationFlaggedBits input) =
      normalizationPivotBits input bit := by
  rw [normalizationPivotBitExpression,
    DeMorgan.Expression.finOr_eval]
  apply congrArg
  funext pivot
  rw [DeMorgan.Expression.eval,
    firstNonzeroFlagExpression_eval_flagged]
  simp only [DeMorgan.Expression.eval,
    normalizationFlaggedBits_vectorBit]

/-- Gate count of one compiled pivot-output expression. -/
@[reducible] def normalizationPivotBitGateCount
    (dimension width : Nat)
    (bit : Fin width) : Nat :=
  (normalizationPivotBitExpression dimension width bit).gateCount

/-- Select the first nonzero field coordinate from a flagged vector. -/
def normalizationPivotFromFlaggedCircuit (dimension width : Nat) :
    Circuit DeMorgan.signature (dimension * width + dimension) width :=
  Circuit.parallelFin width fun bit =>
      (normalizationPivotBitExpression dimension width bit).circuit

@[simp] theorem normalizationPivotFromFlaggedCircuit_size (dimension width : Nat) :
    (normalizationPivotFromFlaggedCircuit dimension width).size =
      ∑ bit, normalizationPivotBitGateCount dimension width bit := by
  simp [normalizationPivotFromFlaggedCircuit, normalizationPivotBitGateCount]

/-- Select the first nonzero coordinate directly from a packed vector. -/
def normalizationPivotCircuit (dimension width : Nat) :=
  (normalizationPivotFromFlaggedCircuit dimension width).comp
    (normalizationFlaggedCircuit dimension width)

/-- The exact gate count of `normalizationPivotCircuit`. -/
@[simp] theorem normalizationPivotCircuit_size
    (dimension width : Nat) :
    (normalizationPivotCircuit dimension width).size =
      (normalizationFlaggedCircuit dimension width).size +
        ∑ bit : Fin width, normalizationPivotBitGateCount dimension width bit := by
  simp [normalizationPivotCircuit]

@[simp] theorem normalizationPivotCircuit_eval
    (input : Fin (dimension * width) -> Bool) :
    (normalizationPivotCircuit dimension width).eval
        DeMorgan.interpretation input =
      normalizationPivotBits input := by
  funext bit
  rw [normalizationPivotCircuit, Circuit.eval_comp,
    normalizationPivotFromFlaggedCircuit,
    Circuit.eval_parallelFin, DeMorgan.Expression.circuit_eval,
    normalizationFlaggedCircuit_eval,
    normalizationPivotBitExpression_eval_flagged]

/-- On a nonzero field vector, pivot selection returns the encoding of its
least nonzero coordinate. -/
theorem normalizationPivotBits_vectorBits
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension)
    (pivotEquality : firstNonzeroCoordinate vector = some pivot) :
    normalizationPivotBits
        (binaryExtensionVectorBits widthPositive vector) =
      decodeBinaryExtension widthPositive (vector pivot) := by
  funext bit
  unfold normalizationPivotBits
  calc
    _ = binaryExtensionVectorBits widthPositive vector
        (finProdFinEquiv (pivot, bit)) := by
      apply DeMorgan.Expression.finOrValue_oneHot dimension pivot
      · exact (firstNonzeroFlag_vectorBits_eq_true_iff widthPositive
          vector pivot).mpr pivotEquality
      · intro other otherTrue
        have otherEquality :=
          (firstNonzeroFlag_vectorBits_eq_true_iff widthPositive
            vector other).mp otherTrue
        exact Option.some.inj (otherEquality.symm.trans pivotEquality)
    _ = decodeBinaryExtension widthPositive (vector pivot) bit := by
      simp [binaryExtensionVectorBits]

/-- Preserve the packed vector while appending its selected pivot. -/
def normalizationVectorAndPivotBits
    (input : Fin (dimension * width) -> Bool) :
    Fin (dimension * width + width) -> Bool :=
  Fin.append input (normalizationPivotBits input)

/-- Shared vector-and-pivot circuit. -/
def normalizationVectorAndPivotCircuit (dimension width : Nat) :=
  (Circuit.id DeMorgan.signature (dimension * width)).parallel
    (normalizationPivotCircuit dimension width)

/-- `normalizationVectorAndPivotCircuit` has exactly the gates of `normalizationPivotCircuit`; the
surrounding wiring adds none. -/
@[simp] theorem normalizationVectorAndPivotCircuit_size
    (dimension width : Nat) :
    (normalizationVectorAndPivotCircuit dimension width).size =
      (normalizationPivotCircuit dimension width).size := by
  simp [normalizationVectorAndPivotCircuit]

@[simp] theorem normalizationVectorAndPivotCircuit_eval
    (input : Fin (dimension * width) -> Bool) :
    (normalizationVectorAndPivotCircuit dimension width).eval
        DeMorgan.interpretation input =
      normalizationVectorAndPivotBits input := by
  simp [normalizationVectorAndPivotCircuit,
    normalizationVectorAndPivotBits]

/-- Preserve the vector block and replace the pivot block by the output of
the shared inverse circuit. -/
noncomputable def normalizationInversePreparationBits
    (widthPositive : 0 < width)
    (input : Fin (dimension * width + width) -> Bool) :
    Fin (dimension * width + width) -> Bool :=
  Fin.append
    (fun index => input (Fin.castAdd width index))
    ((binaryExtensionInverseCircuit widthPositive).eval
      DeMorgan.interpretation
      (fun bit => input (Fin.natAdd (dimension * width) bit)))

/-- Apply one shared pivot inversion while retaining the original vector. -/
noncomputable def normalizationInversePreparationCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :=
  ((Circuit.id DeMorgan.signature (dimension * width + width)).mapOutputs
      (Fin.castAdd width)).parallel
    ((binaryExtensionInverseCircuit widthPositive).mapInputs
      (Fin.natAdd (dimension * width)))

/-- `normalizationInversePreparationCircuit` has exactly the gates of
`binaryExtensionInverseCircuit`; the surrounding wiring adds none. -/
@[simp] theorem normalizationInversePreparationCircuit_size
    (dimension : Nat)
    (widthPositive : 0 < width) :
    (normalizationInversePreparationCircuit dimension widthPositive).size =
      (binaryExtensionInverseCircuit widthPositive).size := by
  simp [normalizationInversePreparationCircuit]

@[simp] theorem normalizationInversePreparationCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin (dimension * width + width) -> Bool) :
    (normalizationInversePreparationCircuit dimension widthPositive).eval
        DeMorgan.interpretation input =
      normalizationInversePreparationBits widthPositive input := by
  rw [normalizationInversePreparationCircuit,
    Circuit.eval_parallel]
  unfold normalizationInversePreparationBits
  congr 1
  rw [Circuit.eval_mapInputs]
  rfl

/-- Vector together with the inverse of its selected pivot. -/
noncomputable def normalizationVectorAndInverseCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :=
  (normalizationInversePreparationCircuit dimension widthPositive).comp
    (normalizationVectorAndPivotCircuit dimension width)

/-- The exact gate count of `normalizationVectorAndInverseCircuit`. -/
@[simp] theorem normalizationVectorAndInverseCircuit_size
    (dimension : Nat)
    (widthPositive : 0 < width) :
    (normalizationVectorAndInverseCircuit dimension widthPositive).size =
      (normalizationVectorAndPivotCircuit dimension width).size +
        (normalizationInversePreparationCircuit dimension widthPositive).size := by
  simp [normalizationVectorAndInverseCircuit]

@[simp] theorem normalizationVectorAndInverseCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool) :
    (normalizationVectorAndInverseCircuit dimension widthPositive).eval
        DeMorgan.interpretation input =
      normalizationInversePreparationBits widthPositive
        (normalizationVectorAndPivotBits input) := by
  rw [normalizationVectorAndInverseCircuit, Circuit.eval_comp,
    normalizationInversePreparationCircuit_eval,
    normalizationVectorAndPivotCircuit_eval]

/-- Wiring from one vector coordinate and the shared inverse block into a
binary-field multiplication circuit. -/
def normalizationCoordinateMultiplicationInput
    (dimension width : Nat)
    (coordinate : Fin dimension) :
    Fin (2 * width) -> Fin (dimension * width + width) :=
  fun input =>
    let sideAndBit :=
      (finProdFinEquiv (m := 2) (n := width)).symm input
    Fin.cases
      (Fin.castAdd width (finProdFinEquiv (coordinate, sideAndBit.2)))
      (fun _ => Fin.natAdd (dimension * width) sideAndBit.2)
      sideAndBit.1

/-- One coordinate times the shared inverse pivot. -/
noncomputable def normalizationCoordinateMultiplicationCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (coordinate : Fin dimension) :=
  (binaryExtensionMulCircuit widthPositive).mapInputs
    (normalizationCoordinateMultiplicationInput dimension width coordinate)

/-- The exact gate count of `normalizationCoordinateMultiplicationCircuit`. -/
@[simp] theorem normalizationCoordinateMultiplicationCircuit_size
    (dimension : Nat)
    (widthPositive : 0 < width)
    (coordinate : Fin dimension) :
    (normalizationCoordinateMultiplicationCircuit dimension widthPositive coordinate).size =
      ∑ output : Fin width, multiplicationCoordinateGateCount widthPositive output := by
  simp [normalizationCoordinateMultiplicationCircuit]

theorem normalizationCoordinateMultiplicationCircuit_eval
    (widthPositive : 0 < width)
    (coordinate : Fin dimension)
    (vector : Fin (dimension * width) -> Bool)
    (inverse : Fin width -> Bool) :
    (normalizationCoordinateMultiplicationCircuit
        dimension widthPositive coordinate).eval
        DeMorgan.interpretation (Fin.append vector inverse) =
      binaryExtensionMulBits widthPositive
        (binaryExtensionPairBits
          (fun bit => vector (finProdFinEquiv (coordinate, bit)))
          inverse) := by
  rw [normalizationCoordinateMultiplicationCircuit,
    Circuit.eval_mapInputs, binaryExtensionMulCircuit_eval]
  congr 1
  funext input
  obtain ⟨⟨side, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := width)).surjective input
  change (Fin.append vector inverse)
      (normalizationCoordinateMultiplicationInput dimension width coordinate
        (finProdFinEquiv (side, bit))) = _
  unfold normalizationCoordinateMultiplicationInput
  rw [Equiv.symm_apply_apply]
  change Fin.append vector inverse
      (Fin.cases
        (Fin.castAdd width (finProdFinEquiv (coordinate, bit)))
        (fun _ => Fin.natAdd (dimension * width) bit) side) =
    binaryExtensionPairBits
      (fun localBit => vector (finProdFinEquiv (coordinate, localBit)))
      inverse (binaryExtensionPairIndex side bit)
  rw [binaryExtensionPairBits_apply]
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · simp only [Fin.cases_zero, Fin.append_left]
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    simp only [Fin.cases_succ, Fin.append_right]

/-- Gate count of one coordinate multiplication. -/
@[reducible] noncomputable def normalizationCoordinateMultiplicationGateCount
    (widthPositive : 0 < width) : Nat :=
  ∑ output, multiplicationCoordinateGateCount widthPositive output

/-- Multiply every vector coordinate by the same shared inverse pivot. -/
noncomputable def normalizationMultiplicationCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :
    Circuit DeMorgan.signature (dimension * width + width)
      (dimension * width) :=
  Circuit.parallelFinVector dimension width
    fun coordinate =>
      normalizationCoordinateMultiplicationCircuit
        dimension widthPositive coordinate

@[simp] theorem normalizationMultiplicationCircuit_size
    (dimension : Nat)
    (widthPositive : 0 < width) :
    (normalizationMultiplicationCircuit dimension widthPositive).size =
      ∑ _ : Fin dimension, normalizationCoordinateMultiplicationGateCount widthPositive := by
  simp [normalizationMultiplicationCircuit, normalizationCoordinateMultiplicationGateCount,
    normalizationCoordinateMultiplicationCircuit]

@[simp] theorem normalizationMultiplicationCircuit_eval
    (widthPositive : 0 < width)
    (vector : Fin (dimension * width) -> Bool)
    (inverse : Fin width -> Bool)
    (coordinate : Fin dimension)
    (bit : Fin width) :
    (normalizationMultiplicationCircuit dimension widthPositive).eval
        DeMorgan.interpretation (Fin.append vector inverse)
        (finProdFinEquiv (coordinate, bit)) =
      binaryExtensionMulBits widthPositive
        (binaryExtensionPairBits
          (fun localBit =>
            vector (finProdFinEquiv (coordinate, localBit)))
          inverse) bit := by
  rw [normalizationMultiplicationCircuit,
    Circuit.eval_parallelFinVector,
    normalizationCoordinateMultiplicationCircuit_eval]

/-- Complete shared circuit for canonical projective normalization. -/
noncomputable def normalizeBinaryExtensionVectorCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :=
  (normalizationMultiplicationCircuit dimension widthPositive).comp
    (normalizationVectorAndInverseCircuit dimension widthPositive)

/-- The exact gate count of `normalizeBinaryExtensionVectorCircuit`. -/
@[simp] theorem normalizeBinaryExtensionVectorCircuit_size
    (dimension : Nat)
    (widthPositive : 0 < width) :
    (normalizeBinaryExtensionVectorCircuit dimension widthPositive).size =
      (normalizationVectorAndInverseCircuit dimension widthPositive).size +
        dimension * normalizationCoordinateMultiplicationGateCount widthPositive := by
  simp [normalizeBinaryExtensionVectorCircuit]

/-- On an encoded nonzero vector, the shared inverse stage preserves the
vector and appends the encoding of the inverse pivot. -/
theorem normalizationVectorAndInverseCircuit_eval_vectorBits
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension)
    (pivotEquality : firstNonzeroCoordinate vector = some pivot) :
    (normalizationVectorAndInverseCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (binaryExtensionVectorBits widthPositive vector) =
      Fin.append
        (binaryExtensionVectorBits widthPositive vector)
        (decodeBinaryExtension widthPositive (vector pivot)⁻¹) := by
  rw [normalizationVectorAndInverseCircuit_eval]
  have pivotNonzero : vector pivot ≠ 0 :=
    (firstNonzeroCoordinate_eq_some_iff vector pivot).mp pivotEquality |>.1
  have selectedPivot := normalizationPivotBits_vectorBits
    widthPositive vector pivot pivotEquality
  funext output
  refine Fin.addCases (fun vectorBit => ?_) (fun inverseBit => ?_) output
  · simp [normalizationInversePreparationBits,
      normalizationVectorAndPivotBits]
  · simp only [normalizationInversePreparationBits, Fin.append_right]
    have tailEquality :
        (fun bit => normalizationVectorAndPivotBits
          (binaryExtensionVectorBits widthPositive vector)
            (Fin.natAdd (dimension * width) bit)) =
          normalizationPivotBits
            (binaryExtensionVectorBits widthPositive vector) := by
      funext bit
      simp [normalizationVectorAndPivotBits]
    rw [tailEquality]
    rw [selectedPivot]
    have inverseCorrect :=
      binaryExtensionInverseCircuit_correct_of_positive widthPositive
        widthAtLeastTwo (decodeBinaryExtension widthPositive (vector pivot))
        (by simpa using pivotNonzero)
    exact congrFun (by simpa using inverseCorrect) inverseBit

/-- The explicit normalization circuit computes the packed canonical
normalization of every nonzero field vector. -/
theorem normalizeBinaryExtensionVectorCircuit_eval_vectorBits
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (vector : Fin dimension -> BinaryExtension width)
    (vectorNonzero : vector ≠ 0) :
    (normalizeBinaryExtensionVectorCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (binaryExtensionVectorBits widthPositive vector) =
      binaryExtensionVectorBits widthPositive
        (normalizeBinaryExtensionVector vector) := by
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
  rw [normalizeBinaryExtensionVectorCircuit, Circuit.eval_comp,
    normalizationVectorAndInverseCircuit_eval_vectorBits widthPositive
      widthAtLeastTwo vector pivot pivotEquality]
  funext output
  obtain ⟨⟨coordinate, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := dimension) (n := width)).surjective output
  rw [normalizationMultiplicationCircuit_eval]
  have coordinateBits :
      (fun localBit => binaryExtensionVectorBits widthPositive vector
        (finProdFinEquiv (coordinate, localBit))) =
      decodeBinaryExtension widthPositive (vector coordinate) := by
    funext localBit
    simp [binaryExtensionVectorBits]
  rw [coordinateBits]
  rw [binaryExtensionMulBits_pair_decode]
  unfold binaryExtensionVectorBits
  rw [Equiv.symm_apply_apply]
  rw [normalizeBinaryExtensionVector_eq_of_firstNonzeroCoordinate
    vector pivot pivotEquality]
  rw [mul_comm]

/-- Consequently the normalization circuit computes the canonical key of
any supplied projective representative. -/
theorem normalizeBinaryExtensionVectorCircuit_eval_projective
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    (normalizeBinaryExtensionVectorCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (binaryExtensionVectorBits widthPositive direction.rep) =
      projectiveDirectionKey widthPositive direction := by
  rw [normalizeBinaryExtensionVectorCircuit_eval_vectorBits widthPositive
    widthAtLeastTwo direction.rep direction.rep_nonzero]
  rfl

/-- A first-nonzero flag expression has quadratic-free, linear cost in the
number of field coordinates. -/
theorem firstNonzeroFlagExpression_standardCost_le
    (pivot : Fin dimension) :
    (firstNonzeroFlagExpression dimension width pivot).standardCost <=
      2 * dimension + 1 := by
  rw [firstNonzeroFlagExpression, DeMorgan.Expression.standardCost,
    DeMorgan.Expression.finAnd_standardCost]
  simp only [DeMorgan.Expression.standardCost, Nat.zero_add]
  have sumBound :
      (∑ previous : Fin dimension,
        (if previous < pivot then
          (DeMorgan.Expression.input
            (normalizationFlagIndex (dimension := dimension)
              (width := width) previous)).not
        else DeMorgan.Expression.constant true).standardCost) <=
      ∑ _previous : Fin dimension, 1 := by
    apply Finset.sum_le_sum
    intro previous _
    split_ifs <;> simp [DeMorgan.Expression.standardCost]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, Nat.mul_one] at sumBound
  omega

/-- One selected-pivot output bit has quadratic cost in the vector
dimension. -/
theorem normalizationPivotBitExpression_standardCost_le
    (bit : Fin width) :
    (normalizationPivotBitExpression dimension width bit).standardCost <=
      dimension * (2 * dimension + 3) := by
  rw [normalizationPivotBitExpression,
    DeMorgan.Expression.finOr_standardCost]
  have termBound : ∀ pivot : Fin dimension,
      ((firstNonzeroFlagExpression dimension width pivot).and
        (.input (normalizationVectorBitIndex
          (finProdFinEquiv (pivot, bit))))).standardCost <=
        2 * dimension + 2 := by
    intro pivot
    simp only [DeMorgan.Expression.standardCost, Nat.add_zero]
    exact Nat.add_le_add_right
      (firstNonzeroFlagExpression_standardCost_le
        (width := width) pivot) 1
  calc
    (∑ pivot : Fin dimension,
        ((firstNonzeroFlagExpression dimension width pivot).and
          (.input (normalizationVectorBitIndex
            (finProdFinEquiv (pivot, bit))))).standardCost) + dimension <=
        (∑ _pivot : Fin dimension, (2 * dimension + 2)) +
          dimension := by
      exact Nat.add_le_add_right
        (Finset.sum_le_sum (s := Finset.univ)
          fun pivot _ => termBound pivot) dimension
    _ = dimension * (2 * dimension + 3) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]
      ring

/-- Cost bound for selecting one shared pivot after the coordinate flags
have been computed. -/
theorem normalizationPivotFromFlaggedCircuit_cost_le :
    (normalizationPivotFromFlaggedCircuit dimension width).cost
        DeMorgan.standardCost <=
      width * (dimension * (2 * dimension + 3)) := by
  rw [normalizationPivotFromFlaggedCircuit,
    Circuit.cost_parallelFin]
  simp only [DeMorgan.Expression.circuit_cost]
  calc
    ∑ bit : Fin width,
        (normalizationPivotBitExpression dimension width bit).standardCost <=
        ∑ _bit : Fin width, dimension * (2 * dimension + 3) := by
      exact Finset.sum_le_sum fun bit _ =>
        normalizationPivotBitExpression_standardCost_le bit
    _ = width * (dimension * (2 * dimension + 3)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul]

/-- Full pivot selection includes the linear coordinate-zero tests. -/
theorem normalizationPivotCircuit_cost_le :
    (normalizationPivotCircuit dimension width).cost
        DeMorgan.standardCost <=
      dimension * width +
        width * (dimension * (2 * dimension + 3)) := by
  rw [normalizationPivotCircuit, Circuit.cost_comp]
  rw [normalizationFlaggedCircuit_cost]
  exact Nat.add_le_add_left
    normalizationPivotFromFlaggedCircuit_cost_le (dimension * width)

@[simp] theorem normalizationCoordinateMultiplicationCircuit_cost
    (widthPositive : 0 < width)
    (coordinate : Fin dimension) :
    (normalizationCoordinateMultiplicationCircuit
        dimension widthPositive coordinate).cost DeMorgan.standardCost =
      width * (6 * (width * width)) := by
  simp [normalizationCoordinateMultiplicationCircuit,
    binaryExtensionMulCircuit_cost]

/-- The final coordinatewise scaling performs one field multiplication per
coordinate. -/
@[simp] theorem normalizationMultiplicationCircuit_cost
    (widthPositive : 0 < width) :
    (normalizationMultiplicationCircuit dimension widthPositive).cost
        DeMorgan.standardCost =
      dimension * (width * (6 * (width * width))) := by
  rw [normalizationMultiplicationCircuit,
    Circuit.cost_parallelFinVector]
  simp only [normalizationCoordinateMultiplicationCircuit_cost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]

@[simp] theorem normalizationInversePreparationCircuit_cost
    (widthPositive : 0 < width) :
    (normalizationInversePreparationCircuit dimension widthPositive).cost
        DeMorgan.standardCost =
      (binaryExtensionInverseCircuit widthPositive).cost
        DeMorgan.standardCost := by
  simp [normalizationInversePreparationCircuit]

/-- A concrete polynomial ledger for the complete projective normalizer. -/
def projectiveNormalizationCircuitBound
    (dimension width : Nat) : Nat :=
  dimension * width +
    width * (dimension * (2 * dimension + 3)) +
    12 * width ^ 4 +
    dimension * (width * (6 * (width * width)))

/-- The complete canonical-normalization circuit satisfies the displayed
polynomial bound. -/
theorem normalizeBinaryExtensionVectorCircuit_cost_le
    (widthPositive : 0 < width) :
    (normalizeBinaryExtensionVectorCircuit dimension widthPositive).cost
        DeMorgan.standardCost <=
      projectiveNormalizationCircuitBound dimension width := by
  rw [normalizeBinaryExtensionVectorCircuit, Circuit.cost_comp,
    normalizationVectorAndInverseCircuit, Circuit.cost_comp,
    normalizationInversePreparationCircuit_cost,
    normalizationVectorAndPivotCircuit]
  simp only [Circuit.cost_parallel, Circuit.cost_id,
    zero_add, normalizationMultiplicationCircuit_cost]
  unfold projectiveNormalizationCircuitBound
  exact Nat.add_le_add
    (Nat.add_le_add normalizationPivotCircuit_cost_le
      (binaryExtensionInverseCircuit_cost_le_fourth widthPositive))
    (le_refl _)

end MassProduction
end Algebraic
