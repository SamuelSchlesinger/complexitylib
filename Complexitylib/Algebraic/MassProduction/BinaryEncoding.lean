/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Projective
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Fintype.Sort

/-!
# Explicit finite binary encodings

Routing keys need a logarithmic-width representation of finite group indices
and the existing basis-bit representation of affine-space points.  These are
plain encoding functions with ordinary injectivity hypotheses; no serializer
or finite-enumeration instances are introduced.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

/-- Little-endian `width`-bit representation of a bounded natural index. -/
def finiteIndexBits
    (width : Nat)
    (value : Fin count) : Fin width -> Bool :=
  fun bit => Nat.testBit value.val bit.val

/-- The fixed-width representation is injective whenever its numeric range
contains every source index. -/
theorem finiteIndexBits_injective
    (fits : count <= 2 ^ width) :
    Function.Injective (finiteIndexBits (count := count) width) := by
  intro left right equalBits
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases represented : bit < width
  · exact congrFun equalBits ⟨bit, represented⟩
  · have widthLeBit : width <= bit := le_of_not_gt represented
    have leftBound : left.val < 2 ^ bit :=
      (left.isLt.trans_le fits).trans_le
        (Nat.pow_le_pow_right (by omega : 0 < 2) widthLeBit)
    have rightBound : right.val < 2 ^ bit :=
      (right.isLt.trans_le fits).trans_le
        (Nat.pow_le_pow_right (by omega : 0 < 2) widthLeBit)
    rw [Nat.testBit_eq_false_of_lt leftBound,
      Nat.testBit_eq_false_of_lt rightBound]

/-- Row-major fixed-basis bits determine a binary-extension-field vector. -/
theorem binaryExtensionVectorBits_injective
    (widthPositive : 0 < width) :
    Function.Injective
      (binaryExtensionVectorBits (dimension := dimension) widthPositive) := by
  intro left right equalBits
  funext coordinate
  rw [← binaryExtensionVectorCoordinate_vectorBits
      widthPositive left coordinate,
    equalBits,
    binaryExtensionVectorCoordinate_vectorBits]

/-- Explicit matching key for a `(group, affine point)` resource slot. -/
noncomputable def resourceSlotKeyBits
    (widthPositive : 0 < width)
    (groupBitWidth : Nat)
    (slot : Fin groups × (Fin dimension -> BinaryExtension width)) :
    Fin (groupBitWidth + dimension * width) -> Bool :=
  Fin.append (finiteIndexBits groupBitWidth slot.1)
    (binaryExtensionVectorBits widthPositive slot.2)

/-- Group bits followed by field-coordinate bits form an injective slot key. -/
theorem resourceSlotKeyBits_injective
    (widthPositive : 0 < width)
    (groupFits : groups <= 2 ^ groupBitWidth) :
    Function.Injective
      (resourceSlotKeyBits (groups := groups) (dimension := dimension)
        widthPositive groupBitWidth) := by
  intro left right equalKey
  apply Prod.ext
  · apply finiteIndexBits_injective groupFits
    funext bit
    have equalAt := congrFun equalKey
      (Fin.castAdd (dimension * width) bit)
    simpa [resourceSlotKeyBits] using equalAt
  · apply binaryExtensionVectorBits_injective widthPositive
    funext bit
    have equalAt := congrFun equalKey
      (Fin.natAdd groupBitWidth bit)
    simpa [resourceSlotKeyBits] using equalAt

/-- Reserve a leading marker bit for active routing keys. -/
def activeRoutingKey
    (key : Fin keyWidth -> Bool) : Fin (keyWidth + 1) -> Bool :=
  Fin.cons false key

/-- Padding keys live in the disjoint leading-marker half of key space. -/
def paddingRoutingKey
    (tail : Fin keyWidth -> Bool) : Fin (keyWidth + 1) -> Bool :=
  Fin.cons true tail

theorem activeRoutingKey_injective :
    Function.Injective (activeRoutingKey (keyWidth := keyWidth)) := by
  intro left right equal
  funext bit
  have equalAt := congrFun equal bit.succ
  simpa [activeRoutingKey] using equalAt

theorem paddingRoutingKey_ne_activeRoutingKey
    (padding active : Fin keyWidth -> Bool) :
    paddingRoutingKey padding ≠ activeRoutingKey active := by
  intro equal
  have equalAt := congrFun equal (0 : Fin (keyWidth + 1))
  simp [paddingRoutingKey, activeRoutingKey] at equalAt

/-! ## Canonical lexicographic enumeration of all fixed-width keys -/

/-- The increasing enumeration of all Boolean bit vectors in lexicographic
order.  This is noncomputable metadata used to assign fixed resource-slot
wires; it is not evaluated by the circuit. -/
noncomputable def lexBitVectorOrderIso (width : Nat) :
    Fin (2 ^ width) ≃o Lex (Fin width -> Bool) :=
  monoEquivOfFin (Lex (Fin width -> Bool)) (by simp)

/-- Bit vector at one canonical lexicographic position. -/
noncomputable def lexBitVectorAt
    (position : Fin (2 ^ width)) : Fin width -> Bool :=
  ofLex (lexBitVectorOrderIso width position)

/-- Canonical lexicographic position of a bit vector. -/
noncomputable def lexBitVectorIndex
    (bits : Fin width -> Bool) : Fin (2 ^ width) :=
  (lexBitVectorOrderIso width).symm (toLex bits)

@[simp] theorem lexBitVectorAt_index
    (bits : Fin width -> Bool) :
    lexBitVectorAt (lexBitVectorIndex bits) = bits := by
  unfold lexBitVectorAt lexBitVectorIndex
  rw [OrderIso.apply_symm_apply]
  exact ofLex_toLex bits

@[simp] theorem lexBitVectorIndex_at
    (position : Fin (2 ^ width)) :
    lexBitVectorIndex (lexBitVectorAt position) = position := by
  unfold lexBitVectorAt lexBitVectorIndex
  rw [toLex_ofLex, OrderIso.symm_apply_apply]

theorem lexBitVectorAt_injective :
    Function.Injective (lexBitVectorAt (width := width)) := by
  intro left right equal
  rw [← lexBitVectorIndex_at left, equal, lexBitVectorIndex_at]

theorem lexBitVectorAt_strictMono :
    StrictMono (fun position : Fin (2 ^ width) =>
      toLex (lexBitVectorAt position)) := by
  intro left right before
  change lexBitVectorOrderIso width left < lexBitVectorOrderIso width right
  exact (lexBitVectorOrderIso width).lt_iff_lt.mpr before

end MassProduction
end Algebraic
