/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.ConstantTranslations
public import Complexitylib.Algebraic.MassProduction.Nonuniform.EnumeratedClean
public import Complexitylib.Algebraic.MassProduction.ResourcePacking
public import Complexitylib.Algebraic.MassProduction.BinaryEncoding

/-!
# A power-of-two line enumeration with fixed directions

Enumerate all field scalars, marking the zero scalar invalid. The valid
slots are exactly a punctured line. For a fixed nonuniform direction all
scalar multiples are offline constants, so the point-generation circuit
costs at most one gate per output bit.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.PaddedLinePoints

open scoped LinearAlgebra.Projectivization

/-- All field scalars, indexed by exactly `2^width` slots. -/
noncomputable def scalarAt (positive : 0 < width) (slot : Fin (2 ^ width)) : BinaryExtension width :=
  encodeBinaryExtension positive (lexBitVectorAt slot)

/-- Every scalar occurs once. -/
theorem scalarAt_injective (positive : 0 < width) : Function.Injective (scalarAt positive) := by
  intro left right equal
  exact lexBitVectorAt_injective ((encodeBinaryExtension_injective positive) equal)

/-- The padded enumeration covers the whole field. -/
theorem scalarAt_surjective (positive : 0 < width) : Function.Surjective (scalarAt positive) := by
  intro scalar
  refine ⟨lexBitVectorIndex (decodeBinaryExtension positive scalar), ?_⟩
  rw [scalarAt, lexBitVectorAt_index, encodeBinaryExtension_decode]

/-- The zero-scalar slot is padding; every other slot is valid. -/
noncomputable def valid (positive : 0 < width) (slot : Fin (2 ^ width)) : Bool := by
  classical
  exact decide (scalarAt positive slot ≠ 0)

/-- Validity is exactly nonzero scalar membership. -/
theorem valid_eq_true_iff (positive : 0 < width) (slot : Fin (2 ^ width)) :
    valid positive slot = true ↔ scalarAt positive slot ≠ 0 := by
  classical
  simp only [valid, decide_eq_true_eq]

/-- The point at a padded scalar slot of a fixed projective direction. -/
noncomputable def point (positive : 0 < width)
    (target : Fin dimension → BinaryExtension width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (slot : Fin (2 ^ width)) := target + scalarAt positive slot • direction.rep

/-- Points within one line have distinct encodings, including the padded target. -/
theorem pointBits_injective (positive : 0 < width)
    (target : Fin dimension → BinaryExtension width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :
    Function.Injective (fun slot => binaryExtensionVectorBits positive (point positive target direction slot)) := by
  intro left right equal
  have samePoints := (binaryExtensionVectorBits_injective positive) equal
  have sameMultiples := add_left_cancel samePoints
  exact scalarAt_injective positive
    (smul_left_injective (BinaryExtension width) direction.rep_nonzero sameMultiples)

/-- The valid encoded slots are exactly the encoded punctured line. -/
theorem pointSet_eq (positive : 0 < width)
    (target : Fin dimension → BinaryExtension width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :
    EnumeratedClean.pointSet (valid positive)
      (fun slot => binaryExtensionVectorBits positive (point positive target direction slot)) =
      (puncturedLine target direction).image (binaryExtensionVectorBits positive) := by
  classical
  ext bits
  rw [EnumeratedClean.mem_pointSet_iff, Finset.mem_image]
  constructor
  · rintro ⟨slot, validSlot, sameBits⟩
    refine ⟨point positive target direction slot, ?_, sameBits⟩
    apply (memPuncturedLine_iff target direction _).mpr
    exact ⟨scalarAt positive slot, (valid_eq_true_iff positive slot).mp validSlot, rfl⟩
  · rintro ⟨value, inLine, sameBits⟩
    obtain ⟨scalar, nonzero, samePoint⟩ := (memPuncturedLine_iff target direction value).mp inLine
    obtain ⟨slot, sameScalar⟩ := scalarAt_surjective positive scalar
    refine ⟨slot, ?_, ?_⟩
    · exact (valid_eq_true_iff positive slot).mpr (sameScalar ▸ nonzero)
    · simpa only [point, sameScalar, samePoint] using sameBits

/-- Vector addition is bitwise XOR in the fixed binary basis. -/
theorem vectorBits_add (positive : 0 < width)
    (left right : Fin dimension → BinaryExtension width) (bit : Fin (dimension * width)) :
    binaryExtensionVectorBits positive (left + right) bit =
      (binaryExtensionVectorBits positive left bit ^^ binaryExtensionVectorBits positive right bit) := by
  obtain ⟨⟨coordinate, digit⟩, rfl⟩ := finProdFinEquiv.surjective bit
  simp only [binaryExtensionVectorBits, Equiv.symm_apply_apply, Pi.add_apply,
    decodeBinaryExtension_add, Bool.add_eq_xor]

/-- A fixed-direction line generator uses the target bits as its only inputs. -/
noncomputable def circuit (positive : 0 < width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :=
  ConstantTranslations.circuit
    (fun slot => binaryExtensionVectorBits positive (scalarAt positive slot • direction.rep))
    (fun _ bit => (DeMorgan.Wiring.input bit : DeMorgan.Wiring (dimension * width)))

/-- The circuit emits the complete padded affine line in slot order. -/
theorem circuit_eval (positive : 0 < width)
    (target : Fin dimension → BinaryExtension width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (slot : Fin (2 ^ width)) (bit : Fin (dimension * width)) :
    (circuit positive direction).eval DeMorgan.interpretation
      (binaryExtensionVectorBits positive target) (finProdFinEquiv (slot, bit)) =
      binaryExtensionVectorBits positive (point positive target direction slot) bit := by
  rw [circuit, ConstantTranslations.circuit_eval, DeMorgan.Wiring.eval_input]
  exact (vectorBits_add positive target (scalarAt positive slot • direction.rep) bit).symm

/-- At most one charged gate per bit of each of the `2^width` points. -/
theorem circuit_cost_le (positive : 0 < width)
    (direction : ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)) :
    (circuit positive direction).cost DeMorgan.standardCost ≤ 2 ^ width * (dimension * width) :=
  ConstantTranslations.circuit_cost_le _ _

end Algebraic.MassProduction.Nonuniform.PaddedLinePoints
