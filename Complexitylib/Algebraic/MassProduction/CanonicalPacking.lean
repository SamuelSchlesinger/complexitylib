/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.ResourcePacking
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Canonical Boolean-prefix packing

This module formalizes the manuscript's exact placement

`s(a) = I(a) / width`, `j(a) = I(a) % width`,

followed by the `dimension` base-`gridWidth` digits of `s(a)`.  The explicit
`finFunctionFinEquiv` is the base-conversion bijection, so injectivity is a
composition of finite embeddings rather than a cardinality-choice argument.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace CanonicalPacking

/-- Number of interpolation nodes available in each tensor coordinate. -/
@[reducible] noncomputable def gridWidth (dimension width : Nat) : Nat :=
  resourceGridWidth (Nat.card (BinaryExtension width)) dimension

theorem gridWidth_eq
    (widthPositive : 0 < width) :
    gridWidth dimension width = resourceGridWidth (2 ^ width) dimension := by
  unfold gridWidth
  rw [card_binaryExtension widthPositive]

/-- The canonical flat information-bit position for one prefix index. -/
noncomputable def flatPosition
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    Fin (gridWidth dimension width ^ dimension * width) :=
  Fin.castLE packingFits source

/-- Split a flat packed position into its tensor-symbol rank and basis bit. -/
noncomputable def symbolAndBit
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    Fin (gridWidth dimension width ^ dimension) × Fin width :=
  finProdFinEquiv.symm (flatPosition packingFits source)

/-- Canonical tensor-symbol rank `s(a) = I(a) / width`. -/
noncomputable def symbolIndex
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    Fin (gridWidth dimension width ^ dimension) :=
  (symbolAndBit packingFits source).1

/-- Canonical basis coordinate `j(a) = I(a) % width`. -/
noncomputable def bitIndex
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) : Fin width :=
  (symbolAndBit packingFits source).2

/-- The `dimension` little-endian base-`gridWidth` digits of `s(a)`. -/
noncomputable def symbolDigits
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    Fin dimension -> Fin (gridWidth dimension width) :=
  finFunctionFinEquiv.symm (symbolIndex packingFits source)

/-- Manuscript-canonical embedding of all Boolean prefixes into information
symbol coordinates and field-basis coordinates. -/
noncomputable def placement
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width) :
    Fin (2 ^ prefixWidth) ↪
      ((Fin dimension -> Fin (gridWidth dimension width)) × Fin width) where
  toFun source := (symbolDigits packingFits source,
    bitIndex packingFits source)
  inj' := by
    intro left right equal
    have digitEqual :
        symbolDigits packingFits left = symbolDigits packingFits right :=
      congrArg Prod.fst equal
    have symbolEqual :
        symbolIndex packingFits left = symbolIndex packingFits right := by
      apply
        (finFunctionFinEquiv
          (m := gridWidth dimension width) (n := dimension)).symm.injective
      simpa [symbolDigits] using digitEqual
    have bitEqual :
        bitIndex packingFits left = bitIndex packingFits right := by
      exact congrArg
        (fun pair :
          ((Fin dimension -> Fin (gridWidth dimension width)) × Fin width) =>
          pair.2)
        equal
    have pairEqual :
        symbolAndBit packingFits left = symbolAndBit packingFits right := by
      apply Prod.ext
      · exact symbolEqual
      · exact bitEqual
    have flatEqual :
        flatPosition packingFits left = flatPosition packingFits right := by
      apply
        (finProdFinEquiv
          (m := gridWidth dimension width ^ dimension)
          (n := width)).symm.injective
      simpa [symbolAndBit] using pairEqual
    apply Fin.ext
    simpa [flatPosition] using congrArg Fin.val flatEqual

@[simp] theorem placement_first
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    (placement packingFits source).1 = symbolDigits packingFits source := rfl

@[simp] theorem placement_second
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    (placement packingFits source).2 = bitIndex packingFits source := rfl

/-- Under the verified binary-field cardinality, the canonical placement has
exactly the `PackedBitPosition` type used by resource packing. -/
noncomputable def packedPlacement
    (_widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width) :
    Fin (2 ^ prefixWidth) ↪ PackedBitPosition dimension width :=
  placement packingFits

@[simp] theorem packedPlacement_first
    (widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    (packedPlacement widthPositive packingFits source).1 =
      symbolDigits packingFits source := rfl

@[simp] theorem packedPlacement_second
    (widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    (packedPlacement widthPositive packingFits source).2 =
      bitIndex packingFits source := rfl

/-- The packed target's field-basis bits are precisely the fixed-width binary
encodings of the base-conversion digits. -/
theorem packedTargetPoint_bits
    (widthPositive : 0 < width)
    (packingFits :
      2 ^ prefixWidth <= gridWidth dimension width ^ dimension * width)
    (source : Fin (2 ^ prefixWidth)) :
    binaryExtensionVectorBits widthPositive
        (packedTargetPoint widthPositive
          (packedPlacement widthPositive packingFits) source) =
      fun flat =>
        let coordinateAndBit :=
          (finProdFinEquiv (m := dimension) (n := width)).symm flat
        finiteIndexBits width
          (symbolDigits packingFits source coordinateAndBit.1)
          coordinateAndBit.2 := by
  funext flat
  let coordinateAndBit :=
    (finProdFinEquiv (m := dimension) (n := width)).symm flat
  simp [packedTargetPoint, binaryResourceNodes, binaryExtensionVectorBits,
    packedPlacement]

end CanonicalPacking
end MassProduction
end Algebraic
