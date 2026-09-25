/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Arithmetic
public import Complexitylib.Algebraic.Iteration
public import Complexitylib.Algebraic.Parallel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Tactic.NormNum

/-!
# Polynomial-size Boolean circuits for binary-field arithmetic

The mass-production manuscript needs arithmetic in `GF(2^width)` at cost
polynomial in `width`.  Treating a field operation as an arbitrary finite
function would cost exponential size and is not sufficient for the scheduler
ledger.

Here `GF(2^width)` is represented in an arbitrary fixed vector-space basis
over `ZMod 2`.  Addition is coordinatewise XOR.  Multiplication is expanded
through the hardwired basis structure constants, so every output coordinate
is a Boolean polynomial with `width^2` quadratic terms.  The resulting
De Morgan circuit has cubic cost.  This is nonuniform in the basis, exactly
as allowed by the manuscript's circuit model, but its size proof is explicit
and polynomial.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators

/-- The canonical ring map from Boolean-ring bits to `ZMod 2`. -/
def boolToZModTwo : Bool →+* ZMod 2 where
  toFun bit := if bit then 1 else 0
  map_one' := rfl
  map_mul' left right := by
    cases left <;> cases right <;> decide
  map_zero' := rfl
  map_add' left right := by
    cases left <;> cases right <;> decide

theorem boolToZModTwo_injective :
    Function.Injective boolToZModTwo := by
  intro left right equal
  cases left <;> cases right <;> simp [boolToZModTwo] at equal ⊢

/-- Boolean-ring bits are ring-equivalent to the prime field `ZMod 2`. -/
noncomputable def boolEquivZModTwo : Bool ≃+* ZMod 2 :=
  RingEquiv.ofBijective boolToZModTwo <|
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨boolToZModTwo_injective, by simp⟩

/-- The binary extension field of vector-space dimension `width`. -/
abbrev BinaryExtension (width : Nat) := GaloisField 2 width

/-- A fixed `width`-element basis of `GF(2^width)` over its prime field. -/
noncomputable def binaryExtensionBasis
    (width : Nat)
    (widthPositive : 0 < width) :
    Module.Basis (Fin width) (ZMod 2) (BinaryExtension width) :=
  Module.finBasisOfFinrankEq (ZMod 2) (BinaryExtension width)
    (GaloisField.finrank 2 widthPositive.ne')

/-- Encode `width` Boolean coordinates as one element of `GF(2^width)`. -/
noncomputable def encodeBinaryExtension
    (widthPositive : 0 < width)
    (bits : Fin width -> Bool) : BinaryExtension width :=
  (binaryExtensionBasis width widthPositive).equivFun.symm
    (boolEquivZModTwo ∘ bits)

/-- Decode a field element into coordinates in the fixed basis. -/
noncomputable def decodeBinaryExtension
    (widthPositive : 0 < width)
    (value : BinaryExtension width) : Fin width -> Bool :=
  boolEquivZModTwo.symm ∘
    (binaryExtensionBasis width widthPositive).equivFun value

@[simp] theorem decodeBinaryExtension_encode
    (widthPositive : 0 < width)
    (bits : Fin width -> Bool) :
    decodeBinaryExtension widthPositive
        (encodeBinaryExtension widthPositive bits) = bits := by
  funext coordinate
  unfold decodeBinaryExtension encodeBinaryExtension
  have coordinates :=
    (binaryExtensionBasis width widthPositive).equivFun.apply_symm_apply
      (boolEquivZModTwo ∘ bits)
  change boolEquivZModTwo.symm
      ((binaryExtensionBasis width widthPositive).equivFun
        ((binaryExtensionBasis width widthPositive).equivFun.symm
          (boolEquivZModTwo ∘ bits)) coordinate) = bits coordinate
  rw [congrFun coordinates coordinate]
  simp [Function.comp_apply]

@[simp] theorem encodeBinaryExtension_decode
    (widthPositive : 0 < width)
    (value : BinaryExtension width) :
    encodeBinaryExtension widthPositive
        (decodeBinaryExtension widthPositive value) = value := by
  unfold encodeBinaryExtension decodeBinaryExtension
  rw [show boolEquivZModTwo ∘
      (boolEquivZModTwo.symm ∘
        (binaryExtensionBasis width widthPositive).equivFun value) =
      (binaryExtensionBasis width widthPositive).equivFun value by
    funext coordinate
    simp]
  exact (binaryExtensionBasis width widthPositive).equivFun.symm_apply_apply
    value

/-- Encoding bit vectors in the fixed basis is injective. -/
theorem encodeBinaryExtension_injective
    (widthPositive : 0 < width) :
    Function.Injective (encodeBinaryExtension widthPositive) := by
  intro left right equal
  rw [← decodeBinaryExtension_encode widthPositive left,
    ← decodeBinaryExtension_encode widthPositive right, equal]

@[simp] theorem encodeBinaryExtension_zero
    (widthPositive : 0 < width) :
    encodeBinaryExtension widthPositive
        (0 : Fin width -> Bool) = 0 := by
  unfold encodeBinaryExtension
  rw [show boolEquivZModTwo ∘ (0 : Fin width -> Bool) = 0 by
    funext coordinate
    simp [Function.comp_apply, boolEquivZModTwo, boolToZModTwo]]
  exact map_zero (binaryExtensionBasis width widthPositive).equivFun.symm

/-- Zero has the all-zero coordinate vector in the chosen field basis. -/
@[simp] theorem decodeBinaryExtension_zero_bits
    (widthPositive : 0 < width) :
    decodeBinaryExtension widthPositive (0 : BinaryExtension width) = 0 := by
  apply encodeBinaryExtension_injective widthPositive
  rw [encodeBinaryExtension_decode, encodeBinaryExtension_zero]

theorem encodeBinaryExtension_ne_zero_iff
    (widthPositive : 0 < width)
    (bits : Fin width -> Bool) :
    encodeBinaryExtension widthPositive bits ≠ 0 ↔
      ∃ bit, bits bit = true := by
  rw [← encodeBinaryExtension_zero widthPositive]
  rw [encodeBinaryExtension_injective widthPositive |>.ne_iff]
  constructor
  · intro notZero
    by_contra noTrue
    apply notZero
    funext bit
    have : bits bit ≠ true := not_exists.mp noTrue bit
    cases value : bits bit
    · rfl
    · exact (this value).elim
  · rintro ⟨bit, bitTrue⟩ equalZero
    have := congrFun equalZero bit
    simp [bitTrue] at this

/-- Coordinates of an encoded bit string are the corresponding prime-field
bits. -/
theorem binaryExtensionBasis_encode_coordinate
    (widthPositive : 0 < width)
    (bits : Fin width -> Bool)
    (coordinate : Fin width) :
    (binaryExtensionBasis width widthPositive).equivFun
        (encodeBinaryExtension widthPositive bits) coordinate =
      boolEquivZModTwo (bits coordinate) := by
  unfold encodeBinaryExtension
  exact congrFun
    ((binaryExtensionBasis width widthPositive).equivFun.apply_symm_apply
      (boolEquivZModTwo ∘ bits)) coordinate

/-- Mapping a decoded coordinate back to the prime field returns the basis
coordinate of the field element. -/
theorem boolEquivZModTwo_decode_coordinate
    (widthPositive : 0 < width)
    (value : BinaryExtension width)
    (coordinate : Fin width) :
    boolEquivZModTwo (decodeBinaryExtension widthPositive value coordinate) =
      (binaryExtensionBasis width widthPositive).equivFun value coordinate := by
  simp [decodeBinaryExtension, Function.comp_apply]

/-- The chosen representation has exactly `2^width` field elements. -/
theorem card_binaryExtension
    (widthPositive : 0 < width) :
    Nat.card (BinaryExtension width) = 2 ^ width := by
  simpa using GaloisField.card 2 width widthPositive.ne'

/-- Encoding turns coordinatewise XOR into field addition. -/
theorem encodeBinaryExtension_add
    (widthPositive : 0 < width)
    (left right : Fin width -> Bool) :
    encodeBinaryExtension widthPositive (left + right) =
      encodeBinaryExtension widthPositive left +
        encodeBinaryExtension widthPositive right := by
  unfold encodeBinaryExtension
  rw [← map_add]
  congr 1
  funext coordinate
  exact boolEquivZModTwo.map_add (left coordinate) (right coordinate)

/-- One hardwired multiplication structure constant of the fixed field
basis, represented as a Boolean bit. -/
noncomputable def multiplicationStructureBit
    (widthPositive : 0 < width)
    (left right output : Fin width) : Bool :=
  boolEquivZModTwo.symm
    ((binaryExtensionBasis width widthPositive).equivFun
      (binaryExtensionBasis width widthPositive left *
        binaryExtensionBasis width widthPositive right) output)

/-- Multiplication coordinates are bilinear polynomials in the input
coordinates, with the chosen basis multiplication table as coefficients. -/
theorem binaryExtension_mul_coordinate
    (widthPositive : 0 < width)
    (left right : BinaryExtension width)
    (output : Fin width) :
    (binaryExtensionBasis width widthPositive).equivFun (left * right) output =
      ∑ leftCoordinate, ∑ rightCoordinate,
        (binaryExtensionBasis width widthPositive).equivFun
            left leftCoordinate *
          (binaryExtensionBasis width widthPositive).equivFun
            right rightCoordinate *
          (binaryExtensionBasis width widthPositive).equivFun
            (binaryExtensionBasis width widthPositive leftCoordinate *
              binaryExtensionBasis width widthPositive rightCoordinate)
            output := by
  let basis := binaryExtensionBasis width widthPositive
  calc
    basis.equivFun (left * right) output =
        basis.equivFun
          ((∑ leftCoordinate, basis.equivFun left leftCoordinate •
              basis leftCoordinate) *
            (∑ rightCoordinate, basis.equivFun right rightCoordinate •
              basis rightCoordinate)) output := by
        rw [basis.sum_equivFun left, basis.sum_equivFun right]
    _ = _ := by
      simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
      simp [basis]

/-- Row-major index of one bit in a pair of field elements. -/
def binaryExtensionPairIndex
    (side : Fin 2)
    (coordinate : Fin width) : Fin (2 * width) :=
  finProdFinEquiv (side, coordinate)

/-- Select one of the two encoded field elements supplied to a binary field
operation. -/
def binaryExtensionPairInput
    (input : Fin (2 * width) -> Bool)
    (side : Fin 2) : Fin width -> Bool :=
  fun coordinate => input (binaryExtensionPairIndex side coordinate)

/-- One structure-constant term contributing to a field multiplication
coordinate. -/
noncomputable def multiplicationCoordinateTerm
    (widthPositive : 0 < width)
    (output left right : Fin width) :
    Arithmetic.Expression Bool (2 * width) :=
  .mul (.constant (multiplicationStructureBit widthPositive left right output))
    (.mul
      (.input (binaryExtensionPairIndex 0 left))
      (.input (binaryExtensionPairIndex 1 right)))

/-- Boolean polynomial for one output coordinate of field multiplication. -/
noncomputable def multiplicationCoordinateExpression
    (widthPositive : 0 < width)
    (output : Fin width) : Arithmetic.Expression Bool (2 * width) :=
  DeMorgan.ArithmeticExpression.finSum (width * width) fun flat =>
    let coordinates :=
      (finProdFinEquiv (m := width) (n := width)).symm flat
    multiplicationCoordinateTerm widthPositive output
      coordinates.1 coordinates.2

/-- Each multiplication-table term has two Boolean AND nodes. -/
@[simp] theorem multiplicationCoordinateTerm_weightedCost
    (widthPositive : 0 < width)
    (output left right : Fin width) :
    (multiplicationCoordinateTerm widthPositive output left right).weightedCost
        4 1 = 2 := by
  rfl

/-- One multiplication coordinate compiles to exactly `6 * width^2`
standard De Morgan gates: two ANDs and four XOR-implementation gates per
structure-table entry. -/
theorem multiplicationCoordinateExpression_weightedCost
    (widthPositive : 0 < width)
    (output : Fin width) :
    (multiplicationCoordinateExpression widthPositive output).weightedCost
        4 1 = 6 * (width * width) := by
  rw [multiplicationCoordinateExpression,
    DeMorgan.ArithmeticExpression.finSum_weightedCost]
  simp only [multiplicationCoordinateTerm_weightedCost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]
  omega

/-- Multiplication on encoded binary-field values, exposed as a Boolean
vector function. -/
noncomputable def binaryExtensionMulBits
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) : Fin width -> Bool :=
  decodeBinaryExtension widthPositive
    (encodeBinaryExtension widthPositive
        (binaryExtensionPairInput input 0) *
      encodeBinaryExtension widthPositive
        (binaryExtensionPairInput input 1))

/-- The structure-constant expression computes the corresponding decoded
coordinate of field multiplication. -/
theorem multiplicationCoordinateExpression_eval
    (widthPositive : 0 < width)
    (output : Fin width)
    (input : Fin (2 * width) -> Bool) :
    (multiplicationCoordinateExpression widthPositive output).eval id input =
      binaryExtensionMulBits widthPositive input output := by
  unfold binaryExtensionMulBits
  apply boolEquivZModTwo.injective
  rw [boolEquivZModTwo_decode_coordinate]
  rw [binaryExtension_mul_coordinate]
  rw [multiplicationCoordinateExpression,
    DeMorgan.ArithmeticExpression.finSum_eval, map_sum]
  simp only [multiplicationCoordinateTerm, multiplicationStructureBit,
    Arithmetic.Expression.eval, id_eq, map_mul,
    RingEquiv.apply_symm_apply,
    binaryExtensionBasis_encode_coordinate,
    binaryExtensionPairInput, mul_assoc, mul_comm]
  let pairEquiv :=
    (finProdFinEquiv (m := width) (n := width)).symm
  refine (pairEquiv.sum_comp
    (fun coordinates : Fin width × Fin width =>
      boolEquivZModTwo
          (input (binaryExtensionPairIndex 0 coordinates.1)) *
        (boolEquivZModTwo
            (input (binaryExtensionPairIndex 1 coordinates.2)) *
          (binaryExtensionBasis width widthPositive).equivFun
            (binaryExtensionBasis width widthPositive coordinates.1 *
              binaryExtensionBasis width widthPositive coordinates.2)
            output))).trans ?_
  exact Fintype.sum_prod_type'
    (fun leftCoordinate rightCoordinate : Fin width =>
      boolEquivZModTwo
          (input (binaryExtensionPairIndex 0 leftCoordinate)) *
        (boolEquivZModTwo
            (input (binaryExtensionPairIndex 1 rightCoordinate)) *
          (binaryExtensionBasis width widthPositive).equivFun
            (binaryExtensionBasis width widthPositive leftCoordinate *
              binaryExtensionBasis width widthPositive rightCoordinate)
            output))

/-- Gate count produced by compiling one multiplication coordinate. -/
@[reducible] noncomputable def multiplicationCoordinateGateCount
    (widthPositive : 0 < width)
    (output : Fin width) : Nat :=
  DeMorgan.arithmeticTranslation.compiledGateCount
    (multiplicationCoordinateExpression widthPositive output).circuit

/-- Explicit De Morgan circuit for multiplication in `GF(2^width)`. -/
noncomputable def binaryExtensionMulCircuit
    (widthPositive : 0 < width) :
    Circuit DeMorgan.signature (2 * width)
      width :=
  Circuit.parallelFin width fun output =>
      DeMorgan.ArithmeticExpression.circuit
        (multiplicationCoordinateExpression widthPositive output)

@[simp] theorem binaryExtensionMulCircuit_size
    (widthPositive : 0 < width) :
    (binaryExtensionMulCircuit widthPositive).size =
      ∑ output, multiplicationCoordinateGateCount widthPositive output := by
  simp [binaryExtensionMulCircuit, multiplicationCoordinateGateCount,
    DeMorgan.ArithmeticExpression.circuit]

/-- The explicit multiplication circuit has exactly the encoded field
multiplication semantics. -/
@[simp] theorem binaryExtensionMulCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) :
    (binaryExtensionMulCircuit widthPositive).eval
        DeMorgan.interpretation input =
      binaryExtensionMulBits widthPositive input := by
  funext output
  rw [binaryExtensionMulCircuit, Circuit.eval_parallelFin,
    DeMorgan.ArithmeticExpression.circuit_eval,
    multiplicationCoordinateExpression_eval]

/-- Exact standard cost of the structure-constant multiplication circuit. -/
@[simp] theorem binaryExtensionMulCircuit_cost
    (widthPositive : 0 < width) :
    (binaryExtensionMulCircuit widthPositive).cost DeMorgan.standardCost =
      width * (6 * (width * width)) := by
  rw [binaryExtensionMulCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.ArithmeticExpression.circuit_cost,
    multiplicationCoordinateExpression_weightedCost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul]

/-- Cubic field-multiplication cost in a conventional power notation. -/
theorem binaryExtensionMulCircuit_cost_le_cube
    (widthPositive : 0 < width) :
    (binaryExtensionMulCircuit widthPositive).cost DeMorgan.standardCost ≤
      6 * width ^ 3 := by
  rw [binaryExtensionMulCircuit_cost]
  ring_nf
  exact le_rfl

/-- One coordinatewise XOR expression for binary-field addition. -/
def additionCoordinateExpression
    (output : Fin width) : Arithmetic.Expression Bool (2 * width) :=
  .add
    (.input (binaryExtensionPairIndex 0 output))
    (.input (binaryExtensionPairIndex 1 output))

/-- Boolean representation of binary-field addition. -/
def binaryExtensionAddBits
    (input : Fin (2 * width) -> Bool) : Fin width -> Bool :=
  binaryExtensionPairInput input 0 + binaryExtensionPairInput input 1

/-- The coordinatewise XOR representation agrees with addition in the
chosen extension field. -/
theorem encode_binaryExtensionAddBits
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) :
    encodeBinaryExtension widthPositive (binaryExtensionAddBits input) =
      encodeBinaryExtension widthPositive
          (binaryExtensionPairInput input 0) +
        encodeBinaryExtension widthPositive
          (binaryExtensionPairInput input 1) :=
  encodeBinaryExtension_add widthPositive _ _

@[simp] theorem additionCoordinateExpression_eval
    (output : Fin width)
    (input : Fin (2 * width) -> Bool) :
    (additionCoordinateExpression output).eval id input =
      binaryExtensionAddBits input output := by
  rfl

/-- Gate count produced by compiling one addition coordinate. -/
@[reducible] def additionCoordinateGateCount
    (output : Fin width) : Nat :=
  DeMorgan.arithmeticTranslation.compiledGateCount
    (additionCoordinateExpression output).circuit

/-- Explicit coordinatewise De Morgan circuit for binary-field addition. -/
def binaryExtensionAddCircuit (width : Nat) :
    Circuit DeMorgan.signature (2 * width) width :=
  Circuit.parallelFin width fun output =>
    DeMorgan.ArithmeticExpression.circuit
      (additionCoordinateExpression output)

@[simp] theorem binaryExtensionAddCircuit_size (width : Nat) :
    (binaryExtensionAddCircuit width).size =
      ∑ output : Fin width, additionCoordinateGateCount (width := width) output := by
  simp [binaryExtensionAddCircuit, additionCoordinateGateCount,
    DeMorgan.ArithmeticExpression.circuit]

@[simp] theorem binaryExtensionAddCircuit_eval
    (input : Fin (2 * width) -> Bool) :
    (binaryExtensionAddCircuit width).eval DeMorgan.interpretation input =
      binaryExtensionAddBits input := by
  funext output
  rw [binaryExtensionAddCircuit, Circuit.eval_parallelFin,
    DeMorgan.ArithmeticExpression.circuit_eval,
    additionCoordinateExpression_eval]

/-- Field addition costs exactly four standard gates per coordinate with the
chosen four-gate XOR implementation. -/
@[simp] theorem binaryExtensionAddCircuit_cost :
    (binaryExtensionAddCircuit width).cost DeMorgan.standardCost =
      4 * width := by
  rw [binaryExtensionAddCircuit, Circuit.cost_parallelFin]
  simp only [DeMorgan.ArithmeticExpression.circuit_cost]
  simp [additionCoordinateExpression, Arithmetic.Expression.weightedCost,
    Nat.mul_comm]

/-- Free projection of one field element from a row-major pair. -/
def binaryExtensionSideCircuit
    (width : Nat)
    (side : Fin 2) : Circuit DeMorgan.signature (2 * width) width :=
  (Circuit.id DeMorgan.signature (2 * width)).mapOutputs
    (binaryExtensionPairIndex side)

@[simp] theorem binaryExtensionSideCircuit_eval
    (side : Fin 2)
    (input : Fin (2 * width) -> Bool) :
    (binaryExtensionSideCircuit width side).eval
        DeMorgan.interpretation input =
      binaryExtensionPairInput input side := by
  rw [binaryExtensionSideCircuit, Circuit.eval_mapOutputs,
    Circuit.eval_id]
  rfl

@[simp] theorem binaryExtensionSideCircuit_cost
    (side : Fin 2) :
    (binaryExtensionSideCircuit width side).cost DeMorgan.standardCost = 0 := by
  simp [binaryExtensionSideCircuit]

/-- Boolean representation of squaring one encoded field element. -/
noncomputable def binaryExtensionSquareBits
    (widthPositive : 0 < width)
    (input : Fin width -> Bool) : Fin width -> Bool :=
  decodeBinaryExtension widthPositive
    (encodeBinaryExtension widthPositive input *
      encodeBinaryExtension widthPositive input)

/-- Squaring circuit obtained by feeding one input vector to both sides of
the multiplication circuit. -/
noncomputable def binaryExtensionSquareCircuit
    (widthPositive : 0 < width) :=
  (binaryExtensionMulCircuit widthPositive).mapInputs fun flat =>
    ((finProdFinEquiv (m := 2) (n := width)).symm flat).2

@[simp] theorem binaryExtensionSquareCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin width -> Bool) :
    (binaryExtensionSquareCircuit widthPositive).eval
        DeMorgan.interpretation input =
      binaryExtensionSquareBits widthPositive input := by
  rw [binaryExtensionSquareCircuit, Circuit.eval_mapInputs,
    binaryExtensionMulCircuit_eval]
  unfold binaryExtensionMulBits binaryExtensionSquareBits
  congr 3
  · funext coordinate
    change input
      (((finProdFinEquiv (m := 2) (n := width)).symm
        (finProdFinEquiv ((0 : Fin 2), coordinate))).2) = input coordinate
    rw [Equiv.symm_apply_apply]
  · funext coordinate
    change input
      (((finProdFinEquiv (m := 2) (n := width)).symm
        (finProdFinEquiv ((1 : Fin 2), coordinate))).2) = input coordinate
    rw [Equiv.symm_apply_apply]

@[simp] theorem binaryExtensionSquareCircuit_cost
    (widthPositive : 0 < width) :
    (binaryExtensionSquareCircuit widthPositive).cost DeMorgan.standardCost =
      width * (6 * (width * width)) := by
  simp [binaryExtensionSquareCircuit,
    binaryExtensionMulCircuit_cost]

/-- Pack two equally wide bit vectors into the row-major two-block layout. -/
def binaryExtensionPairBits
    (left right : Fin width -> Bool) : Fin (2 * width) -> Bool :=
  fun flat =>
    let indexed := (finProdFinEquiv (m := 2) (n := width)).symm flat
    Fin.cases (left indexed.2) (fun _ => right indexed.2) indexed.1

@[simp] theorem binaryExtensionPairBits_apply
    (left right : Fin width -> Bool)
    (side : Fin 2)
    (coordinate : Fin width) :
    binaryExtensionPairBits left right
        (binaryExtensionPairIndex side coordinate) =
      Fin.cases (left coordinate) (fun _ => right coordinate) side := by
  unfold binaryExtensionPairBits binaryExtensionPairIndex
  rw [Equiv.symm_apply_apply]

@[simp] theorem binaryExtensionPairInput_pairBits_zero
    (left right : Fin width -> Bool) :
    binaryExtensionPairInput (binaryExtensionPairBits left right) 0 = left := by
  funext coordinate
  exact binaryExtensionPairBits_apply left right 0 coordinate

@[simp] theorem binaryExtensionPairInput_pairBits_one
    (left right : Fin width -> Bool) :
    binaryExtensionPairInput (binaryExtensionPairBits left right) 1 = right := by
  funext coordinate
  exact binaryExtensionPairBits_apply left right 1 coordinate

/-- A `parallelPair` circuit has exactly the corresponding packed-pair
semantics. -/
theorem Circuit.eval_parallelPair_eq_binaryExtensionPairBits
    (left : Circuit DeMorgan.signature n width)
    (right : Circuit DeMorgan.signature n width)
    (input : Fin n -> Bool) :
    (left.parallelPair right).eval DeMorgan.interpretation input =
      binaryExtensionPairBits
        (left.eval DeMorgan.interpretation input)
        (right.eval DeMorgan.interpretation input) := by
  funext flat
  obtain ⟨⟨side, coordinate⟩, rfl⟩ :=
    (finProdFinEquiv (m := 2) (n := width)).surjective flat
  rw [Circuit.eval_parallelPair_apply]
  change _ = binaryExtensionPairBits
    (left.eval DeMorgan.interpretation input)
    (right.eval DeMorgan.interpretation input)
      (binaryExtensionPairIndex side coordinate)
  rw [binaryExtensionPairBits_apply]

/-- Squaring the second state component while retaining the two-component
input namespace. -/
noncomputable def binaryExtensionSquareRightCircuit
    (widthPositive : 0 < width) :=
  (binaryExtensionSquareCircuit widthPositive).mapInputs
    (binaryExtensionPairIndex 1)

@[simp] theorem binaryExtensionSquareRightCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) :
    (binaryExtensionSquareRightCircuit widthPositive).eval
        DeMorgan.interpretation input =
      binaryExtensionSquareBits widthPositive
        (binaryExtensionPairInput input 1) := by
  rw [binaryExtensionSquareRightCircuit, Circuit.eval_mapInputs,
    binaryExtensionSquareCircuit_eval]
  rfl

/-- Encoding the squaring output gives the square of the encoded input. -/
@[simp] theorem encode_binaryExtensionSquareBits
    (widthPositive : 0 < width)
    (input : Fin width -> Bool) :
    encodeBinaryExtension widthPositive
        (binaryExtensionSquareBits widthPositive input) =
      encodeBinaryExtension widthPositive input *
        encodeBinaryExtension widthPositive input := by
  unfold binaryExtensionSquareBits
  rw [encodeBinaryExtension_decode]

/-- Encoding the multiplication output gives the product of the two encoded
input blocks. -/
@[simp] theorem encode_binaryExtensionMulBits
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) :
    encodeBinaryExtension widthPositive
        (binaryExtensionMulBits widthPositive input) =
      encodeBinaryExtension widthPositive
          (binaryExtensionPairInput input 0) *
        encodeBinaryExtension widthPositive
          (binaryExtensionPairInput input 1) := by
  unfold binaryExtensionMulBits
  rw [encodeBinaryExtension_decode]

@[simp] theorem binaryExtensionMulBits_pair_decode
    (widthPositive : 0 < width)
    (left right : BinaryExtension width) :
    binaryExtensionMulBits widthPositive
        (binaryExtensionPairBits
          (decodeBinaryExtension widthPositive left)
          (decodeBinaryExtension widthPositive right)) =
      decodeBinaryExtension widthPositive (left * right) := by
  apply encodeBinaryExtension_injective widthPositive
  rw [encode_binaryExtensionMulBits,
    binaryExtensionPairInput_pairBits_zero,
    binaryExtensionPairInput_pairBits_one]
  simp

/-- Inputs for one inverse-state update: the square of the second component,
followed by the unchanged first component. -/
noncomputable def binaryExtensionInverseUpdateInputsCircuit
    (widthPositive : 0 < width) :=
  (binaryExtensionSquareRightCircuit widthPositive).parallelPair
    (binaryExtensionSideCircuit width 0)

@[simp] theorem binaryExtensionInverseUpdateInputsCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) :
    (binaryExtensionInverseUpdateInputsCircuit widthPositive).eval
        DeMorgan.interpretation input =
      binaryExtensionPairBits
        (binaryExtensionSquareBits widthPositive
          (binaryExtensionPairInput input 1))
        (binaryExtensionPairInput input 0) := by
  rw [binaryExtensionInverseUpdateInputsCircuit,
    Circuit.eval_parallelPair_eq_binaryExtensionPairBits,
    binaryExtensionSquareRightCircuit_eval,
    binaryExtensionSideCircuit_eval]

/-- The new second component in one inverse-exponentiation round. -/
noncomputable def binaryExtensionInverseUpdateBits
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) : Fin width -> Bool :=
  binaryExtensionMulBits widthPositive <|
    binaryExtensionPairBits
      (binaryExtensionSquareBits widthPositive
        (binaryExtensionPairInput input 1))
      (binaryExtensionPairInput input 0)

/-- Field-level semantics of one inverse-state update. -/
@[simp] theorem encode_binaryExtensionInverseUpdateBits
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) :
    encodeBinaryExtension widthPositive
        (binaryExtensionInverseUpdateBits widthPositive input) =
      (encodeBinaryExtension widthPositive
          (binaryExtensionPairInput input 1) *
        encodeBinaryExtension widthPositive
          (binaryExtensionPairInput input 1)) *
        encodeBinaryExtension widthPositive
          (binaryExtensionPairInput input 0) := by
  unfold binaryExtensionInverseUpdateBits
  rw [encode_binaryExtensionMulBits,
    binaryExtensionPairInput_pairBits_zero,
    binaryExtensionPairInput_pairBits_one,
    encode_binaryExtensionSquareBits]

/-- One state transition `(x, y) -> (x, y^2 * x)`. -/
noncomputable def binaryExtensionInverseStepBits
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) : Fin (2 * width) -> Bool :=
  binaryExtensionPairBits (binaryExtensionPairInput input 0)
    (binaryExtensionInverseUpdateBits widthPositive input)

/-- De Morgan circuit for one shared inverse-exponentiation state round. -/
noncomputable def binaryExtensionInverseStepCircuit
    (widthPositive : 0 < width) :=
  (binaryExtensionSideCircuit width 0).parallelPair
    ((binaryExtensionMulCircuit widthPositive).comp
      (binaryExtensionInverseUpdateInputsCircuit widthPositive))

@[simp] theorem binaryExtensionInverseStepCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin (2 * width) -> Bool) :
    (binaryExtensionInverseStepCircuit widthPositive).eval
        DeMorgan.interpretation input =
      binaryExtensionInverseStepBits widthPositive input := by
  rw [binaryExtensionInverseStepCircuit,
    Circuit.eval_parallelPair_eq_binaryExtensionPairBits,
    binaryExtensionSideCircuit_eval, Circuit.eval_comp,
    binaryExtensionMulCircuit_eval,
    binaryExtensionInverseUpdateInputsCircuit_eval]
  rfl

/-- One inverse-exponentiation round costs exactly two field
multiplications. -/
@[simp] theorem binaryExtensionInverseStepCircuit_cost
    (widthPositive : 0 < width) :
    (binaryExtensionInverseStepCircuit widthPositive).cost
        DeMorgan.standardCost =
      2 * (width * (6 * (width * width))) := by
  simp [binaryExtensionInverseStepCircuit,
    binaryExtensionInverseUpdateInputsCircuit,
    binaryExtensionSquareRightCircuit,
    binaryExtensionMulCircuit_cost, Nat.mul_comm]
  omega

/-- The exponent recurrence used by the inverse circuit. -/
private theorem inverseExponent_succ (steps : Nat) :
    (2 ^ (steps + 1) - 1) + (2 ^ (steps + 1) - 1) + 1 =
      2 ^ (steps + 2) - 1 := by
  rw [show steps + 2 = (steps + 1) + 1 by omega, pow_succ]
  have positive : 0 < 2 ^ (steps + 1) := pow_pos (by omega) _
  omega

/-- Starting from `(x, x)`, after `steps` rounds the state is
`(x, x^(2^(steps+1)-1))` at the field level. -/
theorem binaryExtensionInverseIteration_encode
    (widthPositive : 0 < width)
    (input : Fin width -> Bool)
    (steps : Nat) :
    let state := Circuit.iterateFunction
      (binaryExtensionInverseStepBits widthPositive) steps
      (binaryExtensionPairBits input input)
    encodeBinaryExtension widthPositive
        (binaryExtensionPairInput state 0) =
        encodeBinaryExtension widthPositive input ∧
      encodeBinaryExtension widthPositive
        (binaryExtensionPairInput state 1) =
        encodeBinaryExtension widthPositive input ^
          (2 ^ (steps + 1) - 1) := by
  induction steps with
  | zero =>
      simp [Circuit.iterateFunction]
  | succ steps inductionHypothesis =>
      rw [Circuit.iterateFunction]
      constructor
      · simp only [binaryExtensionInverseStepBits,
          binaryExtensionPairInput_pairBits_zero]
        exact inductionHypothesis.1
      · simp only [binaryExtensionInverseStepBits,
          binaryExtensionPairInput_pairBits_one,
          encode_binaryExtensionInverseUpdateBits]
        rw [inductionHypothesis.2, inductionHypothesis.1]
        let value := encodeBinaryExtension widthPositive input
        change (value ^ (2 ^ (steps + 1) - 1) *
            value ^ (2 ^ (steps + 1) - 1)) * value =
          value ^ (2 ^ (steps + 2) - 1)
        calc
          _ = value ^
              ((2 ^ (steps + 1) - 1) +
                (2 ^ (steps + 1) - 1)) * value := by
              exact congrArg (fun result => result * value)
                (pow_add value _ _).symm
          _ = value ^
              ((2 ^ (steps + 1) - 1) +
                (2 ^ (steps + 1) - 1) + 1) := by
              exact (pow_succ value _).symm
          _ = _ := by rw [inverseExponent_succ]

/-- Duplicate one encoded field input into the initial inverse state. -/
def binaryExtensionInverseInitialCircuit (width : Nat) :=
  (Circuit.id DeMorgan.signature width).parallelPair
    (Circuit.id DeMorgan.signature width)

@[simp] theorem binaryExtensionInverseInitialCircuit_eval
    (input : Fin width -> Bool) :
    (binaryExtensionInverseInitialCircuit width).eval
        DeMorgan.interpretation input =
      binaryExtensionPairBits input input := by
  rw [binaryExtensionInverseInitialCircuit,
    Circuit.eval_parallelPair_eq_binaryExtensionPairBits]
  simp

@[simp] theorem binaryExtensionInverseInitialCircuit_cost :
    (binaryExtensionInverseInitialCircuit width).cost
        DeMorgan.standardCost = 0 := by
  simp [binaryExtensionInverseInitialCircuit]

/-- State circuit after the fixed `width - 2` inverse-exponentiation
rounds. -/
noncomputable def binaryExtensionInverseStateCircuit
    (widthPositive : 0 < width) :=
  (binaryExtensionInverseStepCircuit widthPositive).iterate (width - 2) |>.comp
    (binaryExtensionInverseInitialCircuit width)

@[simp] theorem binaryExtensionInverseStateCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin width -> Bool) :
    (binaryExtensionInverseStateCircuit widthPositive).eval
        DeMorgan.interpretation input =
      Circuit.iterateFunction
        (binaryExtensionInverseStepBits widthPositive) (width - 2)
        (binaryExtensionPairBits input input) := by
  rw [binaryExtensionInverseStateCircuit, Circuit.eval_comp,
    Circuit.eval_iterate, binaryExtensionInverseInitialCircuit_eval]
  rw [show
    (binaryExtensionInverseStepCircuit widthPositive).eval
        DeMorgan.interpretation =
      binaryExtensionInverseStepBits widthPositive by
    funext state
    exact binaryExtensionInverseStepCircuit_eval widthPositive state]

/-- Select the accumulated exponent before the final squaring. -/
noncomputable def binaryExtensionInversePreSquareCircuit
    (widthPositive : 0 < width) :=
  (binaryExtensionSideCircuit width 1).comp
    (binaryExtensionInverseStateCircuit widthPositive)

/-- Explicit inverse circuit using the addition chain
`x -> x^3 -> x^7 -> ... -> x^(2^(width-1)-1)`, followed by one square. -/
noncomputable def binaryExtensionInverseCircuit
    (widthPositive : 0 < width) :=
  (binaryExtensionSquareCircuit widthPositive).comp
    (binaryExtensionInversePreSquareCircuit widthPositive)

@[simp] theorem binaryExtensionInversePreSquareCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin width -> Bool) :
    (binaryExtensionInversePreSquareCircuit widthPositive).eval
        DeMorgan.interpretation input =
      binaryExtensionPairInput
        (Circuit.iterateFunction
          (binaryExtensionInverseStepBits widthPositive) (width - 2)
          (binaryExtensionPairBits input input)) 1 := by
  rw [binaryExtensionInversePreSquareCircuit, Circuit.eval_comp,
    binaryExtensionSideCircuit_eval,
    binaryExtensionInverseStateCircuit_eval]

@[simp] theorem binaryExtensionInverseCircuit_eval
    (widthPositive : 0 < width)
    (input : Fin width -> Bool) :
    (binaryExtensionInverseCircuit widthPositive).eval
        DeMorgan.interpretation input =
      binaryExtensionSquareBits widthPositive
        (binaryExtensionPairInput
          (Circuit.iterateFunction
            (binaryExtensionInverseStepBits widthPositive) (width - 2)
            (binaryExtensionPairBits input input)) 1) := by
  rw [binaryExtensionInverseCircuit, Circuit.eval_comp,
    binaryExtensionSquareCircuit_eval,
    binaryExtensionInversePreSquareCircuit_eval]

/-- Arithmetic identity closing the inverse addition chain. -/
private theorem inverseExponent_final
    (widthAtLeastTwo : 2 <= width) :
    (2 ^ (width - 2 + 1) - 1) +
        (2 ^ (width - 2 + 1) - 1) =
      2 ^ width - 2 := by
  have predecessor : width - 2 + 1 = width - 1 := by omega
  have powerSucc : 2 ^ width = 2 ^ (width - 1) * 2 := by
    conv_lhs => rw [show width = (width - 1) + 1 by omega, pow_succ]
  rw [predecessor, powerSucc]
  have positive : 0 < 2 ^ (width - 1) := pow_pos (by omega) _
  omega

/-- The field element encoded by the inverse circuit is `x^(2^width-2)`. -/
theorem encode_binaryExtensionInverseCircuit_eval
    (widthAtLeastTwo : 2 <= width)
    (input : Fin width -> Bool) :
    encodeBinaryExtension (lt_of_lt_of_le (by omega) widthAtLeastTwo)
        ((binaryExtensionInverseCircuit
          (lt_of_lt_of_le (by omega) widthAtLeastTwo)).eval
            DeMorgan.interpretation input) =
      encodeBinaryExtension (lt_of_lt_of_le (by omega) widthAtLeastTwo)
          input ^ (2 ^ width - 2) := by
  let widthPositive : 0 < width := lt_of_lt_of_le (by omega) widthAtLeastTwo
  change encodeBinaryExtension widthPositive
      ((binaryExtensionInverseCircuit widthPositive).eval
        DeMorgan.interpretation input) =
    encodeBinaryExtension widthPositive input ^ (2 ^ width - 2)
  rw [binaryExtensionInverseCircuit_eval,
    encode_binaryExtensionSquareBits]
  have accumulated :=
    (binaryExtensionInverseIteration_encode widthPositive input
      (width - 2)).2
  rw [accumulated]
  exact (pow_add (encodeBinaryExtension widthPositive input)
    (2 ^ (width - 2 + 1) - 1)
    (2 ^ (width - 2 + 1) - 1)).symm.trans <|
      congrArg (fun exponent =>
        encodeBinaryExtension widthPositive input ^ exponent)
        (inverseExponent_final widthAtLeastTwo)

/-- In a binary extension field, the penultimate positive power is the
multiplicative inverse of every nonzero element. -/
theorem binaryExtension_pow_card_sub_two_eq_inv
    (widthPositive : 0 < width)
    (value : BinaryExtension width)
    (valueNonzero : value ≠ 0) :
    value ^ (2 ^ width - 2) = value⁻¹ := by
  let _ := Fintype.ofFinite (BinaryExtension width)
  apply eq_inv_of_mul_eq_one_right
  calc
    value * value ^ (2 ^ width - 2) =
        value ^ ((2 ^ width - 2) + 1) :=
      (pow_succ' value (2 ^ width - 2)).symm
    _ = value ^ (2 ^ width - 1) := by
      congr 1
      have atLeastTwo : 2 <= 2 ^ width := by
        exact Nat.succ_le_iff.mpr (Nat.one_lt_two_pow widthPositive.ne')
      omega
    _ = 1 := by
      have cardEquality :
          Fintype.card (BinaryExtension width) = 2 ^ width := by
        rw [← Nat.card_eq_fintype_card,
          card_binaryExtension widthPositive]
      rw [← cardEquality]
      exact FiniteField.pow_card_sub_one_eq_one value valueNonzero

/-- On nonzero inputs, the explicit circuit computes multiplicative
inversion in `GF(2^width)`. -/
theorem binaryExtensionInverseCircuit_correct
    (widthAtLeastTwo : 2 <= width)
    (input : Fin width -> Bool)
    (inputNonzero :
      encodeBinaryExtension (lt_of_lt_of_le (by omega) widthAtLeastTwo)
        input ≠ 0) :
    (binaryExtensionInverseCircuit
        (lt_of_lt_of_le (by omega) widthAtLeastTwo)).eval
          DeMorgan.interpretation input =
      decodeBinaryExtension (lt_of_lt_of_le (by omega) widthAtLeastTwo)
        (encodeBinaryExtension
          (lt_of_lt_of_le (by omega) widthAtLeastTwo) input)⁻¹ := by
  let widthPositive : 0 < width := lt_of_lt_of_le (by omega) widthAtLeastTwo
  apply encodeBinaryExtension_injective widthPositive
  rw [encode_binaryExtensionInverseCircuit_eval widthAtLeastTwo,
    encodeBinaryExtension_decode,
    binaryExtension_pow_card_sub_two_eq_inv widthPositive _ inputNonzero]

/-- Proof-parameter-stable form of inverse-circuit correctness. -/
theorem binaryExtensionInverseCircuit_correct_of_positive
    (widthPositive : 0 < width)
    (widthAtLeastTwo : 2 <= width)
    (input : Fin width -> Bool)
    (inputNonzero : encodeBinaryExtension widthPositive input ≠ 0) :
    (binaryExtensionInverseCircuit widthPositive).eval
          DeMorgan.interpretation input =
      decodeBinaryExtension widthPositive
        (encodeBinaryExtension widthPositive input)⁻¹ := by
  have canonicalPositive : 0 < width :=
    lt_of_lt_of_le (by omega) widthAtLeastTwo
  have positiveEquality : widthPositive = canonicalPositive :=
    Subsingleton.elim _ _
  subst widthPositive
  exact binaryExtensionInverseCircuit_correct widthAtLeastTwo input
    inputNonzero

/-- Exact cost of the inverse addition chain: two multiplications per round,
followed by one final squaring. -/
@[simp] theorem binaryExtensionInverseCircuit_cost
    (widthPositive : 0 < width) :
    (binaryExtensionInverseCircuit widthPositive).cost
        DeMorgan.standardCost =
      (width - 2) * (2 * (width * (6 * (width * width)))) +
        width * (6 * (width * width)) := by
  simp [binaryExtensionInverseCircuit,
    binaryExtensionInversePreSquareCircuit,
    binaryExtensionInverseStateCircuit,
    binaryExtensionInverseStepCircuit_cost,
    binaryExtensionSquareCircuit_cost]

/-- The explicit inversion circuit has quartic Boolean gate cost. -/
theorem binaryExtensionInverseCircuit_cost_le_fourth
    (widthPositive : 0 < width) :
    (binaryExtensionInverseCircuit widthPositive).cost
        DeMorgan.standardCost <= 12 * width ^ 4 := by
  rw [binaryExtensionInverseCircuit_cost]
  let multiplicationCost := width * (6 * (width * width))
  change (width - 2) * (2 * multiplicationCost) +
      multiplicationCost <= 12 * width ^ 4
  calc
    _ = ((width - 2) * 2 + 1) * multiplicationCost := by ring
    _ <= (2 * width) * multiplicationCost := by
      exact Nat.mul_le_mul_right multiplicationCost (by omega)
    _ = 12 * width ^ 4 := by
      simp only [multiplicationCost]
      ring

end MassProduction
end Algebraic
