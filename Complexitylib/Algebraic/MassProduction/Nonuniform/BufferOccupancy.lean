/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferModel

/-!
# Occupancy decoded from completed buffer records

The shared source array consists of every completed request's stored point
slots, with the fixed zero-scalar validity mask. Its represented occupied
set is exactly the encoded union of completed punctured lines.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

open scoped LinearAlgebra.Projectivization

/-- Whole point-address vectors have the expected field encoding. -/
theorem pointWire_vector_eval (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin completed)
    (slot : Fin (2 ^ width)) :
    (fun bit => (BufferInput.pointWire pending requestWidth (finProdFinEquiv (request, slot)) bit).eval
      (input positive state data targets)) =
      binaryExtensionVectorBits positive
        (PaddedLinePoints.point positive (targets (state.order (.inl request))) (state.directions request) slot) := by
  funext bit
  exact pointWire_eval positive state data targets request slot bit

/-- The source array is precisely the completed geometric occupancy. -/
theorem occupied_input (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) :
    MenuPointLayout.occupied
      (BufferInput.pointWire (completed := completed) (slots := 2 ^ width) (keyWidth := dimension * width)
        pending requestWidth)
      (BufferInput.flagWire
        (BufferInput.inputWidth completed pending requestWidth (2 ^ width) (dimension * width))
        (PaddedLinePoints.valid positive))
      (input positive state data targets) =
      (occupied state targets).image (binaryExtensionVectorBits positive) := by
  classical
  ext bits
  rw [MenuPointLayout.mem_occupied_iff, Finset.mem_image]
  constructor
  · rintro ⟨source, sameBits, validSlot⟩
    obtain ⟨⟨request, slot⟩, rfl⟩ := finProdFinEquiv.surjective source
    rw [pointWire_vector_eval] at sameBits
    rw [BufferInput.flagWire_eval, PaddedLinePoints.valid_eq_true_iff] at validSlot
    refine ⟨PaddedLinePoints.point positive (targets (state.order (.inl request))) (state.directions request) slot,
      ?_, sameBits⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨request, Finset.mem_univ _, ?_⟩
    apply (memPuncturedLine_iff _ _ _).mpr
    exact ⟨PaddedLinePoints.scalarAt positive slot, validSlot, rfl⟩
  · rintro ⟨value, inOccupied, sameBits⟩
    obtain ⟨request, _, inLine⟩ := Finset.mem_biUnion.mp inOccupied
    obtain ⟨scalar, nonzero, samePoint⟩ := (memPuncturedLine_iff _ _ _).mp inLine
    obtain ⟨slot, sameScalar⟩ := PaddedLinePoints.scalarAt_surjective positive scalar
    refine ⟨finProdFinEquiv (request, slot), ?_, ?_⟩
    · rw [pointWire_vector_eval]
      simpa only [PaddedLinePoints.point, sameScalar, samePoint] using sameBits
    · rw [BufferInput.flagWire_eval, PaddedLinePoints.valid_eq_true_iff]
      exact sameScalar ▸ nonzero

end Algebraic.MassProduction.Nonuniform.BufferModel
