/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Recovery
public import Complexitylib.Algebraic.MassProduction.BinaryField
public import Complexitylib.Algebraic.MassProduction.BinaryEncoding
public import Mathlib.Data.Fintype.EquivFin

/-!
# Packing Boolean data into evaluation-code resource functions

For a fixed suffix, the manuscript packs requested Boolean values into basis
coordinates of the tensor-code information symbols.  This module states that
packing through an explicit embedding and proves that punctured-line recovery
returns the original Boolean coordinate.

The placement embedding is data, not a serialization typeclass.  A later
front-end circuit may implement any concrete placement satisfying the same
interface without changing the algebraic recovery proof. Packing capacities
use `Nat.card`, so their public types do not capture a field enumeration.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

universe u

variable {Prefix : Type u}

open scoped BigOperators LinearAlgebra.Projectivization

/-- One Boolean information position consists of a tensor-grid symbol and a
basis coordinate inside that binary-extension-field symbol. -/
abbrev PackedBitPosition (dimension width : Nat) :=
  (Fin dimension ->
      Fin (resourceGridWidth (Nat.card (BinaryExtension width)) dimension))
    × Fin width

/-- Concrete interpolation nodes: a grid index is represented by its
little-endian `width`-bit integer and encoded in the fixed field basis.  This
choice connects the semantic evaluation code to the runtime packing circuit. -/
noncomputable def binaryResourceNodes
    (widthPositive : 0 < width)
    (dimension : Nat) :
    Fin (resourceGridWidth
      (Nat.card (BinaryExtension width)) dimension) ->
      BinaryExtension width :=
  fun point => encodeBinaryExtension widthPositive
    (finiteIndexBits width point)

theorem binaryResourceNodes_injective
    (widthPositive : 0 < width)
    (dimension : Nat) :
    Function.Injective (binaryResourceNodes widthPositive dimension) := by
  have gridFits :
      resourceGridWidth (Nat.card (BinaryExtension width)) dimension <=
        2 ^ width := by
    rw [card_binaryExtension widthPositive]
    unfold resourceGridWidth
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  intro left right equal
  apply finiteIndexBits_injective gridFits
  exact encodeBinaryExtension_injective widthPositive equal

/-- Read the source bit assigned to a packed position, using `false` for an
unused information coordinate.  Classical choice is local to this semantic
definition and does not create a global decidability instance. -/
noncomputable def packedBit
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (values : Prefix -> Bool)
    (position : PackedBitPosition dimension width) : Bool := by
  classical
  exact if occupied : ∃ source, placement source = position then
    values (Classical.choose occupied)
  else
    false

/-- A placement embedding makes the lookup at every occupied coordinate
exact. -/
theorem packedBit_at_placement
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (values : Prefix -> Bool)
    (source : Prefix) :
    packedBit placement values (placement source) = values source := by
  classical
  unfold packedBit
  rw [dite_eq_left ⟨source, rfl⟩]
  apply congrArg values
  apply placement.injective
  exact Classical.choose_spec (show ∃ candidate,
    placement candidate = placement source from ⟨source, rfl⟩)

/-- Pack Boolean information coordinates into one field-valued message on
the tensor grid. -/
noncomputable def packedMessage
    (widthPositive : 0 < width)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (values : Prefix -> Bool) :
    (Fin dimension ->
      Fin (resourceGridWidth
        (Nat.card (BinaryExtension width)) dimension)) ->
      BinaryExtension width :=
  fun symbol => encodeBinaryExtension widthPositive fun bit =>
    packedBit placement values (symbol, bit)

/-- Decoding an occupied coordinate of the packed message recovers its
source Boolean value. -/
theorem decode_packedMessage_at_placement
    (widthPositive : 0 < width)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (values : Prefix -> Bool)
    (source : Prefix) :
    decodeBinaryExtension widthPositive
        (packedMessage widthPositive placement values
          (placement source).1)
        (placement source).2 =
      values source := by
  rw [packedMessage, decodeBinaryExtension_encode]
  exact packedBit_at_placement placement values source

/-- Decoding is additive in the fixed binary basis. -/
theorem decodeBinaryExtension_add
    (widthPositive : 0 < width)
    (left right : BinaryExtension width) :
    decodeBinaryExtension widthPositive (left + right) =
      decodeBinaryExtension widthPositive left +
        decodeBinaryExtension widthPositive right := by
  apply encodeBinaryExtension_injective widthPositive
  rw [encodeBinaryExtension_decode, encodeBinaryExtension_add,
    encodeBinaryExtension_decode, encodeBinaryExtension_decode]

/-- Decoding commutes with a finite sum of binary-extension-field values. -/
theorem decodeBinaryExtension_finset_sum
    (widthPositive : 0 < width)
    (set : Finset Index)
    (values : Index -> BinaryExtension width) :
    decodeBinaryExtension widthPositive (∑ index ∈ set, values index) =
      ∑ index ∈ set, decodeBinaryExtension widthPositive (values index) := by
  classical
  induction set using Finset.induction_on with
  | empty => simp [decodeBinaryExtension_zero_bits widthPositive]
  | @insert index set notMember inductionHypothesis =>
      rw [Finset.sum_insert notMember, Finset.sum_insert notMember,
        decodeBinaryExtension_add, inductionHypothesis]

/-- Field-valued resource function induced by one packed Boolean family.
The `Suffix` argument is the shorter input on which recursive evaluation will
operate. -/
noncomputable def packedEvaluationResource
    (widthPositive : 0 < width)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> Suffix -> Bool)
    (point : Fin dimension -> BinaryExtension width)
    (suffix : Suffix) : BinaryExtension width :=
  evaluationCode (binaryResourceNodes widthPositive dimension)
    (packedMessage widthPositive placement
      (fun source => function source suffix)) point

/-- Tensor-grid point containing the bit assigned to one source prefix. -/
noncomputable def packedTargetPoint
    (widthPositive : 0 < width)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (source : Prefix) : Fin dimension -> BinaryExtension width :=
  binaryResourceNodes widthPositive dimension ∘ (placement source).1

/-- The packed target is systematic: its assigned basis coordinate is the
original Boolean function value. -/
theorem packedEvaluationResource_at_target
    (widthPositive : 0 < width)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> Suffix -> Bool)
    (source : Prefix)
    (suffix : Suffix) :
    decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function
          (packedTargetPoint widthPositive placement source) suffix)
        (placement source).2 =
      function source suffix := by
  unfold packedEvaluationResource packedTargetPoint
  rw [evaluationCode_on_grid _
    (binaryResourceNodes_injective widthPositive dimension)]
  exact decode_packedMessage_at_placement widthPositive placement
    (fun candidate => function candidate suffix) source

/-- Exact Boolean-coordinate recovery from any projective punctured line
through the packed information point. -/
theorem packedEvaluationResource_sum_puncturedLine
    (widthPositive : 0 < width)
    (dimensionPositive : 0 < dimension)
    (placement : Prefix ↪ PackedBitPosition dimension width)
    (function : Prefix -> Suffix -> Bool)
    (source : Prefix)
    (suffix : Suffix)
    (direction : ℙ (BinaryExtension width)
      (Fin dimension -> BinaryExtension width)) :
    (∑ point ∈ puncturedLine
        (packedTargetPoint widthPositive placement source) direction,
        decodeBinaryExtension widthPositive
          (packedEvaluationResource widthPositive placement function
            point suffix) (placement source).2) =
      function source suffix := by
  classical
  let _ : Fintype (BinaryExtension width) :=
    Fintype.ofFinite (BinaryExtension width)
  have fieldCardAtLeastTwo : 2 <= Nat.card (BinaryExtension width) := by
    rw [card_binaryExtension widthPositive]
    exact Nat.one_lt_two_pow_iff.mpr (Nat.ne_of_gt widthPositive)
  have degree :
      Fintype.card (Fin dimension) *
          (Fintype.card (Fin (resourceGridWidth
            (Nat.card (BinaryExtension width)) dimension)) - 1) <
        Fintype.card (BinaryExtension width) - 1 := by
    simpa only [Fintype.card_fin, Nat.card_fin,
      ← Nat.card_eq_fintype_card] using
      resourceGridWidth_degree_lt
        (Nat.card (BinaryExtension width)) dimension
        fieldCardAtLeastTwo dimensionPositive
  have fieldRecovery := evaluationCode_sum_puncturedLine
    (binaryResourceNodes widthPositive dimension)
    (packedMessage widthPositive placement
      (fun candidate => function candidate suffix))
    degree
    (packedTargetPoint widthPositive placement source) direction
  have coordinateRecovery := congrArg
    (fun value => decodeBinaryExtension widthPositive value
      (placement source).2) fieldRecovery
  rw [decodeBinaryExtension_finset_sum] at coordinateRecovery
  simp only [Finset.sum_apply] at coordinateRecovery
  change
    decodeBinaryExtension widthPositive
        (packedEvaluationResource widthPositive placement function
          (packedTargetPoint widthPositive placement source) suffix)
        (placement source).2 =
      ∑ point ∈ puncturedLine
        (packedTargetPoint widthPositive placement source) direction,
        decodeBinaryExtension widthPositive
          (packedEvaluationResource widthPositive placement function
            point suffix) (placement source).2
    at coordinateRecovery
  exact coordinateRecovery.symm.trans
    (packedEvaluationResource_at_target widthPositive placement function
      source suffix)

/-- The number of Boolean resource functions is the number of ambient code
points times the extension-field bit width. -/
theorem packedEvaluationResource_count
    (widthPositive : 0 < width) :
    Nat.card (Fin dimension -> BinaryExtension width) * width =
      (2 ^ width) ^ dimension * width := by
  rw [Nat.card_fun, Nat.card_fin, card_binaryExtension widthPositive]

/-- A semantic placement exists whenever the information-bit count fits in
the tensor-grid symbol capacity.  This is deliberately separate from the
later polynomial-size placement circuit. -/
theorem nonempty_packedBitPlacement_of_card_le
    [Fintype Prefix]
    (capacity : Fintype.card Prefix <=
      (resourceGridWidth
        (Nat.card (BinaryExtension width)) dimension) ^ dimension *
          width) :
    Nonempty (Prefix ↪ PackedBitPosition dimension width) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa [PackedBitPosition] using capacity

end MassProduction
end Algebraic
