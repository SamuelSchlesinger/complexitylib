/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BinaryField
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Canonical projective coordinates over binary extension fields

The scheduler ranks forbidden directions by first normalizing a nonzero
vector: its first nonzero coordinate is scaled to one.  This file establishes
the field-level representation and its projective invariance.  The following
circuit module realizes the same normalization using the explicit polynomial-
size field circuits.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped LinearAlgebra.Projectivization

/-- Decode one coordinate from a row-major packed field vector. -/
noncomputable def binaryExtensionVectorCoordinate
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool)
    (coordinate : Fin dimension) : BinaryExtension width :=
  encodeBinaryExtension widthPositive fun bit =>
    input (finProdFinEquiv (coordinate, bit))

/-- Encode a field vector in row-major `(coordinate, bit)` order. -/
noncomputable def binaryExtensionVectorBits
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width) :
    Fin (dimension * width) -> Bool :=
  fun output =>
    let coordinateAndBit :=
      (finProdFinEquiv (m := dimension) (n := width)).symm output
    decodeBinaryExtension widthPositive (vector coordinateAndBit.1)
      coordinateAndBit.2

@[simp] theorem binaryExtensionVectorCoordinate_vectorBits
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (coordinate : Fin dimension) :
    binaryExtensionVectorCoordinate widthPositive
        (binaryExtensionVectorBits widthPositive vector) coordinate =
      vector coordinate := by
  unfold binaryExtensionVectorCoordinate binaryExtensionVectorBits
  rw [show (fun bit =>
      decodeBinaryExtension widthPositive
        (vector
          ((finProdFinEquiv (m := dimension) (n := width)).symm
            (finProdFinEquiv (coordinate, bit))).1)
        ((finProdFinEquiv (m := dimension) (n := width)).symm
          (finProdFinEquiv (coordinate, bit))).2) =
      decodeBinaryExtension widthPositive (vector coordinate) by
    funext bit
    rw [Equiv.symm_apply_apply]]
  exact encodeBinaryExtension_decode widthPositive (vector coordinate)

@[simp] theorem binaryExtensionVectorBits_vectorCoordinate
    (widthPositive : 0 < width)
    (input : Fin (dimension * width) -> Bool) :
    binaryExtensionVectorBits widthPositive
        (binaryExtensionVectorCoordinate widthPositive input) = input := by
  funext output
  unfold binaryExtensionVectorBits binaryExtensionVectorCoordinate
  let coordinateAndBit :=
    (finProdFinEquiv (m := dimension) (n := width)).symm output
  change decodeBinaryExtension widthPositive
      (encodeBinaryExtension widthPositive fun bit =>
        input (finProdFinEquiv (coordinateAndBit.1, bit)))
        coordinateAndBit.2 = input output
  rw [decodeBinaryExtension_encode]
  exact congrArg input (Equiv.apply_symm_apply finProdFinEquiv output)

@[simp] theorem binaryExtensionVectorBits_eq_zero_iff
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width) :
    binaryExtensionVectorBits widthPositive vector = (fun _ => false) ↔
      vector = 0 := by
  constructor
  · intro bitsZero
    funext coordinate
    rw [← binaryExtensionVectorCoordinate_vectorBits
      widthPositive vector coordinate, bitsZero]
    unfold binaryExtensionVectorCoordinate
    rw [show (fun _ : Fin width => false) = 0 by rfl]
    exact encodeBinaryExtension_zero widthPositive
  · intro vectorZero
    rw [vectorZero]
    funext output
    unfold binaryExtensionVectorBits
    simp only [Pi.zero_apply]
    rw [decodeBinaryExtension_zero_bits]
    rfl

theorem binaryExtensionVectorBits_ne_zero_iff
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width) :
    binaryExtensionVectorBits widthPositive vector ≠ (fun _ => false) ↔
      vector ≠ 0 := by
  exact not_congr (binaryExtensionVectorBits_eq_zero_iff
    widthPositive vector)

/-- Least nonzero coordinate of a field vector, if one exists. -/
noncomputable def firstNonzeroCoordinate
    (vector : Fin dimension -> BinaryExtension width) :
    Option (Fin dimension) := by
  classical
  exact if h : ∃ coordinate, vector coordinate ≠ 0 then
    some (Fin.find (fun coordinate => vector coordinate ≠ 0) h)
  else none

/-- Normalize a nonzero vector by its first nonzero coordinate.  The zero
vector is sent to zero. -/
noncomputable def normalizeBinaryExtensionVector
    (vector : Fin dimension -> BinaryExtension width) :
    Fin dimension -> BinaryExtension width :=
  match firstNonzeroCoordinate vector with
  | none => 0
  | some pivot => fun coordinate => vector coordinate * (vector pivot)⁻¹

theorem firstNonzeroCoordinate_eq_some_iff
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension) :
    firstNonzeroCoordinate vector = some pivot ↔
      vector pivot ≠ 0 ∧
        ∀ previous, previous < pivot -> vector previous = 0 := by
  classical
  unfold firstNonzeroCoordinate
  split_ifs with existsNonzero
  · simp only [Option.some.injEq]
    constructor
    · intro equal
      subst pivot
      exact ⟨Fin.find_spec existsNonzero, fun previous previousLt => by
        exact not_ne_iff.mp (Fin.find_min existsNonzero previousLt)⟩
    · rintro ⟨pivotNonzero, previousZero⟩
      apply Fin.ext
      by_contra different
      have ordered :
          Fin.find (fun coordinate => vector coordinate ≠ 0) existsNonzero <
              pivot ∨
            pivot <
              Fin.find (fun coordinate => vector coordinate ≠ 0)
                existsNonzero := by
        omega
      rcases ordered with findLt | pivotLt
      · exact (Fin.find_spec existsNonzero)
          (previousZero _ findLt)
      · exact (Fin.find_min existsNonzero pivotLt) pivotNonzero
  · constructor
    · intro impossible
      cases impossible
    · rintro ⟨pivotNonzero, _⟩
      exact (existsNonzero ⟨pivot, pivotNonzero⟩).elim

theorem firstNonzeroCoordinate_smul
    (vector : Fin dimension -> BinaryExtension width)
    (scalar : BinaryExtension width)
    (scalarNonzero : scalar ≠ 0)
    (vectorNonzero : ∃ coordinate, vector coordinate ≠ 0) :
    firstNonzeroCoordinate (fun coordinate => scalar * vector coordinate) =
      firstNonzeroCoordinate vector := by
  classical
  let pivot :=
    Fin.find (fun coordinate => vector coordinate ≠ 0) vectorNonzero
  have originalPivot : firstNonzeroCoordinate vector = some pivot := by
    simp only [firstNonzeroCoordinate, vectorNonzero, ↓reduceDIte, pivot]
  have pivotProperties :=
    (firstNonzeroCoordinate_eq_some_iff vector pivot).mp originalPivot
  have scaledPivot : firstNonzeroCoordinate
      (fun coordinate => scalar * vector coordinate) = some pivot := by
    apply (firstNonzeroCoordinate_eq_some_iff _ pivot).mpr
    refine ⟨mul_ne_zero scalarNonzero pivotProperties.1, ?_⟩
    intro previous previousLt
    rw [pivotProperties.2 previous previousLt, mul_zero]
  exact scaledPivot.trans originalPivot.symm

theorem normalizeBinaryExtensionVector_smul
    (vector : Fin dimension -> BinaryExtension width)
    (scalar : BinaryExtension width)
    (scalarNonzero : scalar ≠ 0)
    (vectorNonzero : ∃ coordinate, vector coordinate ≠ 0) :
    normalizeBinaryExtensionVector
        (fun coordinate => scalar * vector coordinate) =
      normalizeBinaryExtensionVector vector := by
  unfold normalizeBinaryExtensionVector
  rw [firstNonzeroCoordinate_smul vector scalar scalarNonzero vectorNonzero]
  generalize firstEquality : firstNonzeroCoordinate vector = first
  cases first with
  | none => rfl
  | some pivot =>
      funext coordinate
      change (scalar * vector coordinate) * (scalar * vector pivot)⁻¹ =
        vector coordinate * (vector pivot)⁻¹
      rw [mul_inv_rev]
      calc
        (scalar * vector coordinate) *
            ((vector pivot)⁻¹ * scalar⁻¹) =
            (scalar * scalar⁻¹) *
              (vector coordinate * (vector pivot)⁻¹) := by ring
        _ = vector coordinate * (vector pivot)⁻¹ := by
          rw [mul_inv_cancel₀ scalarNonzero, one_mul]

theorem normalizeBinaryExtensionVector_eq_of_firstNonzeroCoordinate
    (vector : Fin dimension -> BinaryExtension width)
    (pivot : Fin dimension)
    (pivotEquality : firstNonzeroCoordinate vector = some pivot) :
    normalizeBinaryExtensionVector vector =
      fun coordinate => (vector pivot)⁻¹ * vector coordinate := by
  unfold normalizeBinaryExtensionVector
  rw [pivotEquality]
  funext coordinate
  exact mul_comm _ _

theorem normalizeBinaryExtensionVector_ne_zero
    (vector : Fin dimension -> BinaryExtension width)
    (vectorNonzero : vector ≠ 0) :
    normalizeBinaryExtensionVector vector ≠ 0 := by
  classical
  have existsNonzero : ∃ coordinate, vector coordinate ≠ 0 := by
    by_contra noneNonzero
    apply vectorNonzero
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp noneNonzero coordinate)
  let pivot :=
    Fin.find (fun coordinate => vector coordinate ≠ 0) existsNonzero
  have pivotEquality : firstNonzeroCoordinate vector = some pivot := by
    simp only [firstNonzeroCoordinate, existsNonzero, ↓reduceDIte, pivot]
  have pivotNonzero :=
    (firstNonzeroCoordinate_eq_some_iff vector pivot).mp pivotEquality |>.1
  intro normalizedZero
  have atPivot := congrFun normalizedZero pivot
  change normalizeBinaryExtensionVector vector pivot = 0 at atPivot
  rw [normalizeBinaryExtensionVector_eq_of_firstNonzeroCoordinate
    vector pivot pivotEquality] at atPivot
  change (vector pivot)⁻¹ * vector pivot = 0 at atPivot
  rw [inv_mul_cancel₀ pivotNonzero] at atPivot
  exact one_ne_zero atPivot

theorem mk_normalizeBinaryExtensionVector
    (vector : Fin dimension -> BinaryExtension width)
    (vectorNonzero : vector ≠ 0) :
    Projectivization.mk (BinaryExtension width)
        (normalizeBinaryExtensionVector vector)
        (normalizeBinaryExtensionVector_ne_zero vector vectorNonzero) =
      Projectivization.mk (BinaryExtension width) vector vectorNonzero := by
  classical
  have existsNonzero : ∃ coordinate, vector coordinate ≠ 0 := by
    by_contra noneNonzero
    apply vectorNonzero
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp noneNonzero coordinate)
  let pivot :=
    Fin.find (fun coordinate => vector coordinate ≠ 0) existsNonzero
  have pivotEquality : firstNonzeroCoordinate vector = some pivot := by
    simp only [firstNonzeroCoordinate, existsNonzero, ↓reduceDIte, pivot]
  apply (Projectivization.mk_eq_mk_iff'
    (BinaryExtension width) _ _ _ _).mpr
  refine ⟨(vector pivot)⁻¹, ?_⟩
  rw [normalizeBinaryExtensionVector_eq_of_firstNonzeroCoordinate
    vector pivot pivotEquality]
  funext coordinate
  simp only [Pi.smul_apply, smul_eq_mul]

theorem normalizeBinaryExtensionVector_rep_mk
    (vector : Fin dimension -> BinaryExtension width)
    (vectorNonzero : vector ≠ 0) :
    normalizeBinaryExtensionVector
        (Projectivization.mk (BinaryExtension width)
          vector vectorNonzero).rep =
      normalizeBinaryExtensionVector vector := by
  let direction := Projectivization.mk (BinaryExtension width)
    vector vectorNonzero
  have representativeEquality : Projectivization.mk (BinaryExtension width)
      direction.rep direction.rep_nonzero =
      Projectivization.mk (BinaryExtension width) vector vectorNonzero :=
    direction.mk_rep
  obtain ⟨scalar, scalarVector⟩ :=
    (Projectivization.mk_eq_mk_iff'
      (BinaryExtension width) direction.rep vector
        direction.rep_nonzero vectorNonzero).mp representativeEquality
  have scalarNonzero : scalar ≠ 0 := by
    intro scalarZero
    rw [scalarZero, zero_smul] at scalarVector
    exact direction.rep_nonzero scalarVector.symm
  have existsNonzero : ∃ coordinate, vector coordinate ≠ 0 := by
    by_contra noneNonzero
    apply vectorNonzero
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp noneNonzero coordinate)
  rw [← scalarVector]
  rw [show scalar • vector =
      (fun coordinate => scalar * vector coordinate) by
    funext coordinate
    simp only [Pi.smul_apply, smul_eq_mul]]
  exact normalizeBinaryExtensionVector_smul vector scalar scalarNonzero
    existsNonzero

/-- Packed canonical key of a projective direction. -/
noncomputable def projectiveDirectionKey
    (widthPositive : 0 < width)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    Fin (dimension * width) -> Bool :=
  binaryExtensionVectorBits widthPositive
    (normalizeBinaryExtensionVector direction.rep)

theorem projectiveDirectionKey_mk
    (widthPositive : 0 < width)
    (vector : Fin dimension -> BinaryExtension width)
    (vectorNonzero : vector ≠ 0) :
    projectiveDirectionKey widthPositive
        (Projectivization.mk (BinaryExtension width)
          vector vectorNonzero) =
      binaryExtensionVectorBits widthPositive
        (normalizeBinaryExtensionVector vector) := by
  unfold projectiveDirectionKey
  rw [normalizeBinaryExtensionVector_rep_mk vector vectorNonzero]

/-- Canonical packed projective keys are injective. -/
theorem projectiveDirectionKey_injective
    (widthPositive : 0 < width) :
    Function.Injective
      (projectiveDirectionKey widthPositive :
        ℙ (BinaryExtension width)
          (Fin dimension -> BinaryExtension width) ->
        (Fin (dimension * width) -> Bool)) := by
  intro left right keysEqual
  have normalizedEqual :
      normalizeBinaryExtensionVector left.rep =
        normalizeBinaryExtensionVector right.rep := by
    funext coordinate
    rw [← binaryExtensionVectorCoordinate_vectorBits widthPositive
        (normalizeBinaryExtensionVector left.rep) coordinate,
      ← binaryExtensionVectorCoordinate_vectorBits widthPositive
        (normalizeBinaryExtensionVector right.rep) coordinate]
    unfold projectiveDirectionKey at keysEqual
    exact congrArg
      (fun bits =>
        binaryExtensionVectorCoordinate widthPositive bits coordinate)
      keysEqual
  have normalizedMkEqual : Projectivization.mk (BinaryExtension width)
        (normalizeBinaryExtensionVector left.rep)
        (normalizeBinaryExtensionVector_ne_zero left.rep left.rep_nonzero) =
      Projectivization.mk (BinaryExtension width)
        (normalizeBinaryExtensionVector right.rep)
        (normalizeBinaryExtensionVector_ne_zero right.rep
          right.rep_nonzero) := by
    apply (Projectivization.mk_eq_mk_iff'
      (BinaryExtension width) _ _ _ _).mpr
    refine ⟨1, ?_⟩
    rw [one_smul]
    exact normalizedEqual.symm
  calc
    left = Projectivization.mk (BinaryExtension width)
        (normalizeBinaryExtensionVector left.rep)
        (normalizeBinaryExtensionVector_ne_zero left.rep
          left.rep_nonzero) :=
      ((mk_normalizeBinaryExtensionVector left.rep left.rep_nonzero).trans
        left.mk_rep).symm
    _ = Projectivization.mk (BinaryExtension width)
        (normalizeBinaryExtensionVector right.rep)
        (normalizeBinaryExtensionVector_ne_zero right.rep
          right.rep_nonzero) := normalizedMkEqual
    _ = right :=
      (mk_normalizeBinaryExtensionVector right.rep right.rep_nonzero).trans
        right.mk_rep

end MassProduction
end Algebraic
