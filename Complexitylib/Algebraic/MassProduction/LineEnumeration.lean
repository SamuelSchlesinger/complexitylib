/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SchedulerStage

/-!
# Explicit enumeration of a punctured affine line

Given packed field vectors for a target and a direction, this module emits
`q - 1` packed points `target + scalar * direction`, one for every nonzero
scalar of `GF(q)`, where `q = 2^width`.  The scalar enumeration is a fixed
noncomputable equivalence used only to hardwire constants; the resulting
Boolean circuit is completely explicit and has the manuscript's
`q * poly(width)` cost shape.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace LineEnumeration

open scoped LinearAlgebra.Projectivization
open Sorting

/-- Nonzero scalars of the selected binary extension field. -/
abbrev NonzeroScalar (width : Nat) :=
  {scalar : BinaryExtension width // scalar ≠ 0}

/-- Exact number of nonzero scalars, kept instance-free in public types. -/
noncomputable def nonzeroScalarCount (width : Nat) : Nat :=
  Nat.card (NonzeroScalar width)

theorem nonzeroScalarCount_eq_two_pow_sub_one
    (widthPositive : 0 < width) :
    nonzeroScalarCount width = 2 ^ width - 1 := by
  classical
  let _ := Fintype.ofFinite (BinaryExtension width)
  unfold nonzeroScalarCount
  rw [Nat.card_eq_fintype_card]
  rw [show Fintype.card (NonzeroScalar width) =
      Fintype.card (BinaryExtension width) - 1 by simp]
  rw [← Nat.card_eq_fintype_card,
    card_binaryExtension widthPositive]

/-- A fixed enumeration of every nonzero scalar. -/
noncomputable def enumeratedNonzeroScalar
    (index : Fin (nonzeroScalarCount width)) : BinaryExtension width :=
  ((Finite.equivFin (NonzeroScalar width)).symm index).1

theorem enumeratedNonzeroScalar_ne_zero
    (index : Fin (nonzeroScalarCount width)) :
    enumeratedNonzeroScalar index ≠ (0 : BinaryExtension width) :=
  ((Finite.equivFin (NonzeroScalar width)).symm index).2

theorem enumeratedNonzeroScalar_surjective
    (scalar : BinaryExtension width)
    (scalarNonzero : scalar ≠ 0) :
    ∃ index : Fin (nonzeroScalarCount width),
      enumeratedNonzeroScalar index = scalar := by
  let nonzero : NonzeroScalar width := ⟨scalar, scalarNonzero⟩
  refine ⟨Finite.equivFin (NonzeroScalar width) nonzero, ?_⟩
  simp [enumeratedNonzeroScalar, nonzero]

theorem enumeratedNonzeroScalar_injective :
    Function.Injective
      (enumeratedNonzeroScalar :
        Fin (nonzeroScalarCount width) -> BinaryExtension width) := by
  intro left right equal
  apply (Finite.equivFin (NonzeroScalar width)).symm.injective
  apply Subtype.ext
  exact equal

/-! ## Fixed scalar and vector-coordinate circuits -/

/-- Compile a hardwired Boolean vector.  Constants contribute internal
nodes but zero standard cost. -/
def constantBitVectorCircuit
    (inputWidth : Nat)
    (bits : Fin width -> Bool) :
    Circuit DeMorgan.signature inputWidth
      (∑ bit, (DeMorgan.Expression.constant
        (n := inputWidth) (bits bit)).gateCount) width :=
  Circuit.parallelFin width
    (fun bit => (DeMorgan.Expression.constant
      (n := inputWidth) (bits bit)).gateCount)
    fun bit => (DeMorgan.Expression.constant
      (n := inputWidth) (bits bit)).circuit

@[simp] theorem constantBitVectorCircuit_eval
    (input : Fin inputWidth -> Bool) :
    (constantBitVectorCircuit inputWidth bits).eval
        DeMorgan.interpretation input = bits := by
  funext bit
  rw [constantBitVectorCircuit, Circuit.eval_parallelFin,
    DeMorgan.Expression.circuit_eval]
  rfl

@[simp] theorem constantBitVectorCircuit_cost :
    (constantBitVectorCircuit inputWidth bits).cost
        DeMorgan.standardCost = 0 := by
  rw [constantBitVectorCircuit, Circuit.cost_parallelFin]
  simp [DeMorgan.Expression.circuit_cost,
    DeMorgan.Expression.standardCost]

/-- Select one field-coordinate block from the target/direction pair. -/
def lineInputCoordinateCircuit
    (dimension width : Nat)
    (side : Fin 2)
    (coordinate : Fin dimension) :
    Circuit DeMorgan.signature (2 * (dimension * width)) 0 width :=
  (Circuit.id DeMorgan.signature (2 * (dimension * width))).mapOutputs
    fun bit => finProdFinEquiv
      (side, finProdFinEquiv (coordinate, bit))

@[simp] theorem lineInputCoordinateCircuit_eval
    (input : Fin (2 * (dimension * width)) -> Bool)
    (side : Fin 2)
    (coordinate : Fin dimension) :
    (lineInputCoordinateCircuit dimension width side coordinate).eval
        DeMorgan.interpretation input =
      fun bit => input
        (finProdFinEquiv (side, finProdFinEquiv (coordinate, bit))) := by
  rw [lineInputCoordinateCircuit, Circuit.eval_mapOutputs,
    Circuit.eval_id]
  rfl

@[simp] theorem lineInputCoordinateCircuit_cost
    (side : Fin 2)
    (coordinate : Fin dimension) :
    (lineInputCoordinateCircuit dimension width side coordinate).cost
        DeMorgan.standardCost = 0 := by
  simp [lineInputCoordinateCircuit]

/-- Packed `(target, direction)` vector pair. -/
noncomputable def lineInputBits
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width) :
    Fin (2 * (dimension * width)) -> Bool :=
  binaryExtensionPairBits
    (binaryExtensionVectorBits widthPositive target)
    (binaryExtensionVectorBits widthPositive direction)

theorem lineInputCoordinateCircuit_eval_lineInput
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width)
    (coordinate : Fin dimension) :
    (lineInputCoordinateCircuit dimension width 0 coordinate).eval
        DeMorgan.interpretation
        (lineInputBits widthPositive target direction) =
      decodeBinaryExtension widthPositive (target coordinate) := by
  funext bit
  rw [lineInputCoordinateCircuit_eval]
  change binaryExtensionPairInput
      (binaryExtensionPairBits
        (binaryExtensionVectorBits widthPositive target)
        (binaryExtensionVectorBits widthPositive direction)) 0
      (finProdFinEquiv (coordinate, bit)) = _
  rw [binaryExtensionPairInput_pairBits_zero]
  simp [binaryExtensionVectorBits]

theorem lineInputDirectionCircuit_eval_lineInput
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width)
    (coordinate : Fin dimension) :
    (lineInputCoordinateCircuit dimension width 1 coordinate).eval
        DeMorgan.interpretation
        (lineInputBits widthPositive target direction) =
      decodeBinaryExtension widthPositive (direction coordinate) := by
  funext bit
  rw [lineInputCoordinateCircuit_eval]
  change binaryExtensionPairInput
      (binaryExtensionPairBits
        (binaryExtensionVectorBits widthPositive target)
        (binaryExtensionVectorBits widthPositive direction)) 1
      (finProdFinEquiv (coordinate, bit)) = _
  rw [binaryExtensionPairInput_pairBits_one]
  simp [binaryExtensionVectorBits]

/-- Multiply one direction coordinate by one hardwired nonzero scalar. -/
noncomputable def directionScalarProductCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (coordinate : Fin dimension)
    (scalar : Fin (nonzeroScalarCount width)) :=
  (binaryExtensionMulCircuit widthPositive).comp
    ((lineInputCoordinateCircuit dimension width 1 coordinate).parallelPair
      (constantBitVectorCircuit (2 * (dimension * width))
        (decodeBinaryExtension widthPositive
          (enumeratedNonzeroScalar scalar))))

@[simp] theorem directionScalarProductCircuit_eval_lineInput
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width)
    (coordinate : Fin dimension)
    (scalar : Fin (nonzeroScalarCount width)) :
    (directionScalarProductCircuit dimension widthPositive
        coordinate scalar).eval DeMorgan.interpretation
        (lineInputBits widthPositive target direction) =
      decodeBinaryExtension widthPositive
        (direction coordinate * enumeratedNonzeroScalar scalar) := by
  rw [directionScalarProductCircuit, Circuit.eval_comp,
    binaryExtensionMulCircuit_eval,
    Circuit.eval_parallelPair_eq_binaryExtensionPairBits,
    lineInputDirectionCircuit_eval_lineInput,
    constantBitVectorCircuit_eval]
  apply encodeBinaryExtension_injective widthPositive
  rw [encode_binaryExtensionMulBits,
    binaryExtensionPairInput_pairBits_zero,
    binaryExtensionPairInput_pairBits_one,
    encodeBinaryExtension_decode, encodeBinaryExtension_decode,
    encodeBinaryExtension_decode]

@[simp] theorem directionScalarProductCircuit_cost
    (widthPositive : 0 < width)
    (coordinate : Fin dimension)
    (scalar : Fin (nonzeroScalarCount width)) :
    (directionScalarProductCircuit dimension widthPositive
        coordinate scalar).cost DeMorgan.standardCost =
      width * (6 * (width * width)) := by
  rw [directionScalarProductCircuit, Circuit.cost_comp,
    Circuit.cost_parallelPair, lineInputCoordinateCircuit_cost,
    constantBitVectorCircuit_cost, binaryExtensionMulCircuit_cost]
  omega

/-- Add the target coordinate to a hardwired scalar multiple of the
direction coordinate. -/
noncomputable def linePointCoordinateCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (coordinate : Fin dimension)
    (scalar : Fin (nonzeroScalarCount width)) :=
  (binaryExtensionAddCircuit width).comp
    ((lineInputCoordinateCircuit dimension width 0 coordinate).parallelPair
      (directionScalarProductCircuit dimension widthPositive
        coordinate scalar))

@[simp] theorem linePointCoordinateCircuit_eval_lineInput
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width)
    (coordinate : Fin dimension)
    (scalar : Fin (nonzeroScalarCount width)) :
    (linePointCoordinateCircuit dimension widthPositive
        coordinate scalar).eval DeMorgan.interpretation
        (lineInputBits widthPositive target direction) =
      decodeBinaryExtension widthPositive
        (target coordinate +
          enumeratedNonzeroScalar scalar * direction coordinate) := by
  rw [linePointCoordinateCircuit, Circuit.eval_comp,
    binaryExtensionAddCircuit_eval,
    Circuit.eval_parallelPair_eq_binaryExtensionPairBits,
    lineInputCoordinateCircuit_eval_lineInput,
    directionScalarProductCircuit_eval_lineInput]
  apply encodeBinaryExtension_injective widthPositive
  rw [encode_binaryExtensionAddBits,
    binaryExtensionPairInput_pairBits_zero,
    binaryExtensionPairInput_pairBits_one,
    encodeBinaryExtension_decode, encodeBinaryExtension_decode,
    encodeBinaryExtension_decode]
  congr 1
  exact mul_comm _ _

@[simp] theorem linePointCoordinateCircuit_cost
    (widthPositive : 0 < width)
    (coordinate : Fin dimension)
    (scalar : Fin (nonzeroScalarCount width)) :
    (linePointCoordinateCircuit dimension widthPositive
        coordinate scalar).cost DeMorgan.standardCost =
      width * (6 * (width * width)) + 4 * width := by
  rw [linePointCoordinateCircuit, Circuit.cost_comp,
    Circuit.cost_parallelPair, lineInputCoordinateCircuit_cost,
    directionScalarProductCircuit_cost, binaryExtensionAddCircuit_cost]
  omega

/-- Named gate count and a type-stable wrapper for one coordinate. -/
@[reducible] noncomputable def linePointCoordinateGateCount
    (dimension : Nat)
    (widthPositive : 0 < width)
    (_coordinate : Fin dimension)
    (scalar : Fin (nonzeroScalarCount width)) : Nat :=
  0 +
    (0 +
      (∑ bit, (DeMorgan.Expression.constant
        (n := 2 * (dimension * width))
        (decodeBinaryExtension widthPositive
          (enumeratedNonzeroScalar scalar) bit)).gateCount) +
      (∑ output, multiplicationCoordinateGateCount
        widthPositive output)) +
    (∑ output : Fin width, additionCoordinateGateCount output)

/-- Emit one complete affine-line point. -/
noncomputable def linePointCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (scalar : Fin (nonzeroScalarCount width)) :=
  Circuit.parallelFinVector dimension width
    (fun coordinate => linePointCoordinateGateCount
      dimension widthPositive coordinate scalar)
    fun coordinate =>
      linePointCoordinateCircuit
        dimension widthPositive coordinate scalar

@[simp] theorem linePointCircuit_eval_lineInput
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width)
    (scalar : Fin (nonzeroScalarCount width)) :
    (linePointCircuit dimension widthPositive scalar).eval
        DeMorgan.interpretation
        (lineInputBits widthPositive target direction) =
      binaryExtensionVectorBits widthPositive
        (target + enumeratedNonzeroScalar scalar • direction) := by
  funext output
  obtain ⟨⟨coordinate, bit⟩, rfl⟩ :=
    (finProdFinEquiv (m := dimension) (n := width)).surjective output
  rw [linePointCircuit, Circuit.eval_parallelFinVector,
    linePointCoordinateCircuit_eval_lineInput]
  unfold binaryExtensionVectorBits
  rw [Equiv.symm_apply_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

@[simp] theorem linePointCircuit_cost
    (widthPositive : 0 < width)
    (scalar : Fin (nonzeroScalarCount width)) :
    (linePointCircuit dimension widthPositive scalar).cost
        DeMorgan.standardCost =
      dimension *
        (width * (6 * (width * width)) + 4 * width) := by
  rw [linePointCircuit, Circuit.cost_parallelFinVector]
  simp only [linePointCoordinateCircuit_cost, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

/-- Named gate count and type-stable wrapper for one complete point. -/
@[reducible] noncomputable def linePointGateCount
    (dimension : Nat)
    (widthPositive : 0 < width)
    (scalar : Fin (nonzeroScalarCount width)) : Nat :=
  ∑ coordinate : Fin dimension,
    linePointCoordinateGateCount dimension widthPositive coordinate scalar

/-- Emit all `q - 1` non-target points in row-major scalar/vector order. -/
noncomputable def lineEnumerationCircuit
    (dimension : Nat)
    (widthPositive : 0 < width) :=
  Circuit.parallelFinVector (nonzeroScalarCount width) (dimension * width)
    (fun scalar => linePointGateCount dimension widthPositive scalar)
    fun scalar => linePointCircuit dimension widthPositive scalar

@[simp] theorem lineEnumerationCircuit_eval_apply
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width)
    (scalar : Fin (nonzeroScalarCount width))
    (bit : Fin (dimension * width)) :
    (lineEnumerationCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (lineInputBits widthPositive target direction)
        (finProdFinEquiv (scalar, bit)) =
      binaryExtensionVectorBits widthPositive
        (target + enumeratedNonzeroScalar scalar • direction) bit := by
  rw [lineEnumerationCircuit, Circuit.eval_parallelFinVector,
    linePointCircuit_eval_lineInput]

/-- Decoding one emitted record gives the intended affine-line point. -/
theorem decode_lineEnumerationCircuit_record
    (widthPositive : 0 < width)
    (target direction : Fin dimension -> BinaryExtension width)
    (scalar : Fin (nonzeroScalarCount width)) :
    binaryExtensionVectorCoordinate widthPositive
        (directProductInput
          ((lineEnumerationCircuit dimension widthPositive).eval
            DeMorgan.interpretation
            (lineInputBits widthPositive target direction)) scalar) =
      target + enumeratedNonzeroScalar scalar • direction := by
  rw [show directProductInput
      ((lineEnumerationCircuit dimension widthPositive).eval
        DeMorgan.interpretation
        (lineInputBits widthPositive target direction)) scalar =
      binaryExtensionVectorBits widthPositive
        (target + enumeratedNonzeroScalar scalar • direction) by
    funext bit
    exact lineEnumerationCircuit_eval_apply
      widthPositive target direction scalar bit]
  funext coordinate
  exact binaryExtensionVectorCoordinate_vectorBits
    widthPositive _ coordinate

/-- Exact polynomial gate ledger for enumerating all nonzero points of one
affine line. -/
@[simp] theorem lineEnumerationCircuit_cost
    (widthPositive : 0 < width) :
    (lineEnumerationCircuit dimension widthPositive).cost
        DeMorgan.standardCost =
      nonzeroScalarCount width *
        (dimension *
          (width * (6 * (width * width)) + 4 * width)) := by
  rw [lineEnumerationCircuit, Circuit.cost_parallelFinVector]
  simp only [linePointCircuit_cost, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

/-- The same ledger with the exact field-size count made explicit. -/
theorem lineEnumerationCircuit_cost_eq_two_pow_sub_one
    (widthPositive : 0 < width) :
    (lineEnumerationCircuit dimension widthPositive).cost
        DeMorgan.standardCost =
      (2 ^ width - 1) *
        (dimension *
          (width * (6 * (width * width)) + 4 * width)) := by
  rw [lineEnumerationCircuit_cost,
    nonzeroScalarCount_eq_two_pow_sub_one widthPositive]

/-! ## Exact finite-set semantics -/

/-- The finite set represented by the enumerator's output records.  Classical
decidable equality is confined to the definition rather than exported as an
instance requirement. -/
noncomputable def enumeratedPuncturedLine
    (target direction : Fin dimension -> BinaryExtension width) :
    Finset (Fin dimension -> BinaryExtension width) := by
  classical
  exact Finset.univ.image fun scalar : Fin (nonzeroScalarCount width) =>
    target + enumeratedNonzeroScalar scalar • direction

/-- Enumerating the normalized representative of a projective direction
produces exactly its punctured affine line, independent of the representative
chosen internally by `Projectivization.rep`. -/
theorem enumeratedPuncturedLine_normalized_eq
    (target : Fin dimension -> BinaryExtension width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    enumeratedPuncturedLine target
        (normalizeBinaryExtensionVector direction.rep) =
      ForbiddenRanks.binaryExtensionPuncturedLine target direction := by
  classical
  let _ := Fintype.ofFinite (BinaryExtension width)
  let normalized := normalizeBinaryExtensionVector direction.rep
  have normalizedNonzero : normalized ≠ 0 :=
    normalizeBinaryExtensionVector_ne_zero direction.rep
      direction.rep_nonzero
  have enumerationEquality :
      enumeratedPuncturedLine target normalized =
        (Finset.univ.erase (0 : BinaryExtension width)).image
          (fun scalar => target + scalar • normalized) := by
    ext point
    constructor
    · intro pointMember
      rw [enumeratedPuncturedLine, Finset.mem_image] at pointMember
      obtain ⟨index, _, pointEquality⟩ := pointMember
      apply Finset.mem_image.mpr
      refine ⟨enumeratedNonzeroScalar index, ?_, pointEquality⟩
      exact Finset.mem_erase.mpr
        ⟨enumeratedNonzeroScalar_ne_zero index, Finset.mem_univ _⟩
    · intro pointMember
      rw [Finset.mem_image] at pointMember
      obtain ⟨scalar, scalarMember, pointEquality⟩ := pointMember
      have scalarNonzero : scalar ≠ 0 :=
        (Finset.mem_erase.mp scalarMember).1
      obtain ⟨index, scalarEquality⟩ :=
        enumeratedNonzeroScalar_surjective scalar scalarNonzero
      rw [enumeratedPuncturedLine, Finset.mem_image]
      refine ⟨index, Finset.mem_univ _, ?_⟩
      rw [scalarEquality]
      exact pointEquality
  have directionEquality :
      Projectivization.mk (BinaryExtension width)
          normalized normalizedNonzero = direction := by
    exact (mk_normalizeBinaryExtensionVector direction.rep
      direction.rep_nonzero).trans direction.mk_rep
  change enumeratedPuncturedLine target normalized =
    puncturedLine target direction
  calc
    enumeratedPuncturedLine target normalized =
        (Finset.univ.erase (0 : BinaryExtension width)).image
          (fun scalar => target + scalar • normalized) :=
      enumerationEquality
    _ = puncturedLine target
        (Projectivization.mk (BinaryExtension width)
          normalized normalizedNonzero) :=
      (puncturedLine_mk_eq_image target normalized
        normalizedNonzero).symm
    _ = puncturedLine target direction := by rw [directionEquality]

/-! ## Scheduler-to-line composition -/

/-- Free projection of the target vector from a scheduler-stage input. -/
def schedulerStageTargetCircuit
    (dimension width depth : Nat) :
    Circuit DeMorgan.signature
      ((networkRecords depth + 1) * (dimension * width)) 0
      (dimension * width) :=
  (Circuit.id DeMorgan.signature
    ((networkRecords depth + 1) * (dimension * width))).mapOutputs
      (SchedulerStage.stageTargetInputIndex depth (dimension * width))

@[simp] theorem schedulerStageTargetCircuit_eval
    (input : Fin ((networkRecords depth + 1) *
      (dimension * width)) -> Bool) :
    (schedulerStageTargetCircuit dimension width depth).eval
        DeMorgan.interpretation input =
      input ∘ SchedulerStage.stageTargetInputIndex
        depth (dimension * width) := by
  rw [schedulerStageTargetCircuit, Circuit.eval_mapOutputs,
    Circuit.eval_id]

@[simp] theorem schedulerStageTargetCircuit_cost :
    (schedulerStageTargetCircuit dimension width depth).cost
        DeMorgan.standardCost = 0 := by
  simp [schedulerStageTargetCircuit]

theorem schedulerStageTargetCircuit_eval_stageInput
    (widthPositive : 0 < width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width) :
    (schedulerStageTargetCircuit dimension width depth).eval
        DeMorgan.interpretation
        (SchedulerStage.schedulerStageInputBits
          widthPositive points target) =
      binaryExtensionVectorBits widthPositive target := by
  funext bit
  rw [schedulerStageTargetCircuit_eval]
  exact SchedulerStage.schedulerStageInputBits_target
    widthPositive points target bit

/-- One fixed circuit that selects a fresh projective direction and emits
all non-target points on the resulting affine line. -/
noncomputable def scheduledLineEnumerationCircuit
    (dimension : Nat)
    (widthPositive : 0 < width)
    (depth : Nat) :=
  (lineEnumerationCircuit dimension widthPositive).comp
    ((schedulerStageTargetCircuit dimension width depth).parallelPair
      (SchedulerStage.schedulerStageCircuit
        dimension widthPositive depth))

/-- Decode an emitted row-major array of packed field vectors as a finite
set.  Classical equality remains local to this boundary. -/
noncomputable def decodedLineOutputSet
    (widthPositive : 0 < width)
    (output : Fin (nonzeroScalarCount width * (dimension * width)) -> Bool) :
    Finset (Fin dimension -> BinaryExtension width) := by
  classical
  exact Finset.univ.image fun scalar : Fin (nonzeroScalarCount width) =>
    binaryExtensionVectorCoordinate widthPositive
      (directProductInput output scalar)

/-- Input-layout-general form of scheduler-and-enumerator correctness. -/
theorem scheduledLineEnumerationCircuit_sound_input_of_nonzero_capacity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (input : Fin ((networkRecords depth + 1) *
      (dimension * width)) -> Bool)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (pointBits : ∀ record bit,
      input (SchedulerStage.stagePointInputIndex
          depth (dimension * width) record bit) =
        binaryExtensionVectorBits widthPositive (points record) bit)
    (targetBits : ∀ bit,
      input (SchedulerStage.stageTargetInputIndex
          depth (dimension * width) bit) =
        binaryExtensionVectorBits widthPositive target bit)
    (capacity :
      (SchedulerStage.pointDifferentIndices points target).card <
        Nat.card (ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (∀ scalar : Fin (nonzeroScalarCount width),
        binaryExtensionVectorCoordinate widthPositive
            (directProductInput
              ((scheduledLineEnumerationCircuit
                dimension widthPositive depth).eval
                DeMorgan.interpretation input) scalar) =
          target + enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector direction.rep) ∧
      decodedLineOutputSet widthPositive
          ((scheduledLineEnumerationCircuit
            dimension widthPositive depth).eval
            DeMorgan.interpretation input) =
        ForbiddenRanks.binaryExtensionPuncturedLine target direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        (SchedulerStage.pointArraySet points) := by
  classical
  have pointsCovered : ∀ point,
      point ∈ SchedulerStage.pointArraySet points ->
        ∃ record, points record = point := by
    intro point pointMember
    unfold SchedulerStage.pointArraySet at pointMember
    rw [Finset.mem_image] at pointMember
    obtain ⟨record, _, equality⟩ := pointMember
    exact ⟨record, equality⟩
  obtain ⟨direction, directionKey, disjoint⟩ :=
    SchedulerStage.schedulerStageCircuit_disjoint_of_nonzero_capacity
      widthPositive widthAtLeastTwo input points target
      (SchedulerStage.pointArraySet points) pointBits targetBits
      pointsCovered capacity
  have targetEvaluation :
      (schedulerStageTargetCircuit dimension width depth).eval
          DeMorgan.interpretation input =
        binaryExtensionVectorBits widthPositive target := by
    funext bit
    rw [schedulerStageTargetCircuit_eval]
    exact targetBits bit
  have pairedInput :
      ((schedulerStageTargetCircuit dimension width depth).parallelPair
        (SchedulerStage.schedulerStageCircuit
          dimension widthPositive depth)).eval
          DeMorgan.interpretation input =
        lineInputBits widthPositive target
          (normalizeBinaryExtensionVector direction.rep) := by
    rw [Circuit.eval_parallelPair_eq_binaryExtensionPairBits,
      targetEvaluation, directionKey]
    rfl
  have recordCorrect : ∀ scalar : Fin (nonzeroScalarCount width),
      binaryExtensionVectorCoordinate widthPositive
          (directProductInput
            ((scheduledLineEnumerationCircuit
              dimension widthPositive depth).eval
              DeMorgan.interpretation input) scalar) =
        target + enumeratedNonzeroScalar scalar •
          normalizeBinaryExtensionVector direction.rep := by
    intro scalar
    rw [scheduledLineEnumerationCircuit, Circuit.eval_comp, pairedInput]
    exact decode_lineEnumerationCircuit_record widthPositive target
      (normalizeBinaryExtensionVector direction.rep) scalar
  have outputSetEquality :
      decodedLineOutputSet widthPositive
          ((scheduledLineEnumerationCircuit
            dimension widthPositive depth).eval
            DeMorgan.interpretation input) =
        enumeratedPuncturedLine target
          (normalizeBinaryExtensionVector direction.rep) := by
    unfold decodedLineOutputSet enumeratedPuncturedLine
    apply Finset.image_congr
    intro scalar _
    exact recordCorrect scalar
  refine ⟨direction, recordCorrect, ?_, disjoint⟩
  exact outputSetEquality.trans
    (enumeratedPuncturedLine_normalized_eq target direction)

/-- The scheduler and enumerator compose end to end: every output record is
the prescribed point of one projective punctured line, the decoded output set
is exactly that line, and it avoids every supplied occupied point. -/
theorem scheduledLineEnumerationCircuit_sound_of_nonzero_capacity
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (capacity :
      (SchedulerStage.pointDifferentIndices points target).card <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (∀ scalar : Fin (nonzeroScalarCount width),
        binaryExtensionVectorCoordinate widthPositive
            (directProductInput
              ((scheduledLineEnumerationCircuit
                dimension widthPositive depth).eval
                DeMorgan.interpretation
                (SchedulerStage.schedulerStageInputBits
                  widthPositive points target)) scalar) =
          target + enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector direction.rep) ∧
      decodedLineOutputSet widthPositive
          ((scheduledLineEnumerationCircuit
            dimension widthPositive depth).eval
            DeMorgan.interpretation
            (SchedulerStage.schedulerStageInputBits
              widthPositive points target)) =
        ForbiddenRanks.binaryExtensionPuncturedLine target direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        (SchedulerStage.pointArraySet points) := by
  classical
  obtain ⟨direction, directionKey, disjoint⟩ :=
    SchedulerStage.schedulerStageCircuit_disjoint_all_points_of_nonzero_capacity
      widthPositive widthAtLeastTwo points target capacity
  let stageInput := SchedulerStage.schedulerStageInputBits
    widthPositive points target
  have pairedInput :
      ((schedulerStageTargetCircuit dimension width depth).parallelPair
        (SchedulerStage.schedulerStageCircuit
          dimension widthPositive depth)).eval
          DeMorgan.interpretation stageInput =
        lineInputBits widthPositive target
          (normalizeBinaryExtensionVector direction.rep) := by
    rw [Circuit.eval_parallelPair_eq_binaryExtensionPairBits,
      schedulerStageTargetCircuit_eval_stageInput, directionKey]
    rfl
  have recordCorrect : ∀ scalar : Fin (nonzeroScalarCount width),
      binaryExtensionVectorCoordinate widthPositive
          (directProductInput
            ((scheduledLineEnumerationCircuit
              dimension widthPositive depth).eval
              DeMorgan.interpretation stageInput) scalar) =
        target + enumeratedNonzeroScalar scalar •
          normalizeBinaryExtensionVector direction.rep := by
    intro scalar
    rw [scheduledLineEnumerationCircuit, Circuit.eval_comp, pairedInput]
    exact decode_lineEnumerationCircuit_record widthPositive target
      (normalizeBinaryExtensionVector direction.rep) scalar
  have outputSetEquality :
      decodedLineOutputSet widthPositive
          ((scheduledLineEnumerationCircuit
            dimension widthPositive depth).eval
            DeMorgan.interpretation stageInput) =
        enumeratedPuncturedLine target
          (normalizeBinaryExtensionVector direction.rep) := by
    unfold decodedLineOutputSet enumeratedPuncturedLine
    apply Finset.image_congr
    intro scalar _
    exact recordCorrect scalar
  refine ⟨direction, recordCorrect, ?_, disjoint⟩
  exact outputSetEquality.trans
    (enumeratedPuncturedLine_normalized_eq target direction)

/-- The total-array capacity condition is a convenient sufficient form of
the end-to-end scheduler-and-enumerator theorem. -/
theorem scheduledLineEnumerationCircuit_sound
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 ≤ width)
    (points : Fin (networkRecords depth) ->
      Fin dimension -> BinaryExtension width)
    (target : Fin dimension -> BinaryExtension width)
    (capacity : networkRecords depth <
      Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width))) :
    ∃ direction : ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width),
      (∀ scalar : Fin (nonzeroScalarCount width),
        binaryExtensionVectorCoordinate widthPositive
            (directProductInput
              ((scheduledLineEnumerationCircuit
                dimension widthPositive depth).eval
                DeMorgan.interpretation
                (SchedulerStage.schedulerStageInputBits
                  widthPositive points target)) scalar) =
          target + enumeratedNonzeroScalar scalar •
            normalizeBinaryExtensionVector direction.rep) ∧
      decodedLineOutputSet widthPositive
          ((scheduledLineEnumerationCircuit
            dimension widthPositive depth).eval
            DeMorgan.interpretation
            (SchedulerStage.schedulerStageInputBits
              widthPositive points target)) =
        ForbiddenRanks.binaryExtensionPuncturedLine target direction ∧
      Disjoint
        (ForbiddenRanks.binaryExtensionPuncturedLine target direction)
        (SchedulerStage.pointArraySet points) := by
  apply scheduledLineEnumerationCircuit_sound_of_nonzero_capacity
    widthPositive widthAtLeastTwo points target
  calc
    (SchedulerStage.pointDifferentIndices points target).card ≤
        (Finset.univ : Finset (Fin (networkRecords depth))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = networkRecords depth := by simp
    _ < Nat.card (ℙ (BinaryExtension width)
        (Fin dimension -> BinaryExtension width)) := capacity

/-- Complete gate ledger for fresh-direction selection followed by line
enumeration. -/
def scheduledLineEnumerationCostBound
    (dimension width depth : Nat) : Nat :=
  SchedulerStage.schedulerStageCostBound dimension width depth +
    (2 ^ width - 1) *
      (dimension *
        (width * (6 * (width * width)) + 4 * width))

theorem scheduledLineEnumerationCircuit_cost_le
    (widthPositive : 0 < width) :
    (scheduledLineEnumerationCircuit dimension widthPositive depth).cost
        DeMorgan.standardCost ≤
      scheduledLineEnumerationCostBound dimension width depth := by
  rw [scheduledLineEnumerationCircuit, Circuit.cost_comp,
    Circuit.cost_parallelPair, schedulerStageTargetCircuit_cost,
    lineEnumerationCircuit_cost_eq_two_pow_sub_one widthPositive]
  unfold scheduledLineEnumerationCostBound
  have stageCost := SchedulerStage.schedulerStageCircuit_cost_le
    (dimension := dimension) (depth := depth) widthPositive
  omega

end LineEnumeration
end MassProduction
end Algebraic
