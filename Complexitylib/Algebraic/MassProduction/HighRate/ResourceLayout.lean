/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.BooleanRecovery
public import Complexitylib.Algebraic.MassProduction.FiniteParameters

/-!
# Exact indexing and keys for the high-rate resource bank

The bank contains exactly one Boolean function per code copy, field point,
and basis bit. Only routing keys use ceiling-logarithm index widths; neither
copy nor bit-index padding enlarges the bank's leading cost.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate.ResourceLayout

set_option backward.isDefEq.respectTransparency false

/-- Exact number of Boolean resource functions. -/
def count (copies dimension width : Nat) : Nat := copies * (2 ^ (dimension * width) * width)

/-- Exact row-major index of a code-copy, encoded-point, basis-bit triple. -/
def index (copy : Fin copies) (point : Fin (2 ^ (dimension * width))) (bit : Fin width) :
    Fin (count copies dimension width) := finProdFinEquiv (copy, finProdFinEquiv (point, bit))

/-- Decode the exact bank index into its three finite coordinates. -/
def atIndex (resource : Fin (count copies dimension width)) :
    Fin copies × Fin (2 ^ (dimension * width)) × Fin width :=
  let pair := (finProdFinEquiv (m := copies) (n := 2 ^ (dimension * width) * width)).symm resource
  (pair.1, finProdFinEquiv.symm pair.2)

/-- Index construction and coordinate decoding cancel exactly. -/
theorem atIndex_index (copy : Fin copies) (point : Fin (2 ^ (dimension * width))) (bit : Fin width) :
    atIndex (index copy point bit) = (copy, point, bit) := by
  simp only [index, atIndex, Equiv.symm_apply_apply]

/-- Every index is recovered from its decoded coordinates. -/
theorem index_atIndex (resource : Fin (count copies dimension width)) :
    index (atIndex resource).1 (atIndex resource).2.1 (atIndex resource).2.2 = resource := by
  simp only [index, atIndex, Prod.mk.eta, Equiv.apply_symm_apply]

/-- Routing key width, with exact point bits and logarithmic finite indices. -/
def keyWidth (copyBits dimension width selectorBits : Nat) : Nat := copyBits + (dimension * width + selectorBits)

/-- Fixed resource keys contain copy, point, and basis-bit coordinates. -/
noncomputable def key (copyBits selectorBits : Nat) (resource : Fin (count copies dimension width)) :
    Fin (keyWidth copyBits dimension width selectorBits) → Bool :=
  Fin.append (finiteIndexBits copyBits (atIndex resource).1)
    (Fin.append (lexBitVectorAt (atIndex resource).2.1) (finiteIndexBits selectorBits (atIndex resource).2.2))

/-- Adequate finite-index widths make the fixed resource keys distinct. -/
theorem key_injective (copyFits : copies ≤ 2 ^ copyBits) (selectorFits : width ≤ 2 ^ selectorBits) :
    Function.Injective (key (copies := copies) (dimension := dimension) (width := width) copyBits selectorBits) := by
  intro left right equal
  have sameCopy : (atIndex left).1 = (atIndex right).1 := by
    apply finiteIndexBits_injective copyFits
    funext bit
    simpa only [key, Fin.append_left] using congrFun equal (Fin.castAdd (dimension * width + selectorBits) bit)
  have samePoint : (atIndex left).2.1 = (atIndex right).2.1 := by
    apply lexBitVectorAt_injective
    funext bit
    simpa only [key, Fin.append_right, Fin.append_left] using
      congrFun equal (Fin.natAdd copyBits (Fin.castAdd selectorBits bit))
  have sameBit : (atIndex left).2.2 = (atIndex right).2.2 := by
    apply finiteIndexBits_injective selectorFits
    funext bit
    simpa only [key, Fin.append_right] using congrFun equal (Fin.natAdd copyBits (Fin.natAdd (dimension * width) bit))
  rw [← index_atIndex left, ← index_atIndex right, sameCopy, samePoint, sameBit]

/-- Bank position of a geometric point and its selected field-basis bit. -/
noncomputable def position (positive : 0 < width) (copy : Fin copies)
    (point : Fin dimension → BinaryExtension width) (bit : Fin width) : Fin (count copies dimension width) :=
  index copy (lexBitVectorIndex (binaryExtensionVectorBits positive point)) bit

/-- The key at a geometric position is its expected concatenated encoding. -/
theorem key_position (positive : 0 < width) (copyBits selectorBits : Nat) (copy : Fin copies)
    (point : Fin dimension → BinaryExtension width) (bit : Fin width) :
    key copyBits selectorBits (position positive copy point bit) =
      Fin.append (finiteIndexBits copyBits copy)
        (Fin.append (binaryExtensionVectorBits positive point) (finiteIndexBits selectorBits bit)) := by
  simp only [key, position, atIndex_index, lexBitVectorAt_index]

/-- Decode a bank index's affine point using the fixed binary basis. -/
noncomputable def pointAt (positive : 0 < width) (resource : Fin (count copies dimension width)) :
    Fin dimension → BinaryExtension width :=
  binaryExtensionVectorCoordinate positive (lexBitVectorAt (atIndex resource).2.1)

/-- Geometric indexing followed by point decoding recovers the same point. -/
theorem pointAt_position (positive : 0 < width) (copy : Fin copies)
    (point : Fin dimension → BinaryExtension width) (bit : Fin width) :
    pointAt positive (position positive copy point bit) = point := by
  funext coordinate
  simp only [pointAt, position, atIndex_index, lexBitVectorAt_index,
    binaryExtensionVectorCoordinate_vectorBits]

/-- The Boolean function at each exact bank position. -/
noncomputable def function {Source Suffix : Type*} (positive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (original : Source → Suffix → Bool)
    (resource : Fin (count copies dimension width)) (suffix : Suffix) : Bool :=
  booleanResource positive code placement original (atIndex resource).1 (pointAt positive resource)
    (atIndex resource).2.2 suffix

/-- A selected bank function is exactly the high-rate recovery resource. -/
theorem function_position {Source Suffix : Type*} (positive : 0 < width)
    (code : LineCode (BinaryExtension width) (Fin dimension))
    (placement : Source ↪ InformationBit code copies) (original : Source → Suffix → Bool)
    (copy : Fin copies) (point : Fin dimension → BinaryExtension width) (bit : Fin width) (suffix : Suffix) :
    function positive code placement original (position positive copy point bit) suffix =
      booleanResource positive code placement original copy point bit suffix := by
  rw [function, pointAt_position]
  simp only [position, atIndex_index]

end Algebraic.MassProduction.HighRate.ResourceLayout
