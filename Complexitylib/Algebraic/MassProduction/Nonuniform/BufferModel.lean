/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferOrder
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseOutput

/-!
# Semantic model of the halving scheduler buffer

Completed and pending positions partition the original request identities.
Completed records store a direction's full affine point list; validity flags
turn these stored lists into exactly the occupied punctured lines.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

open scoped LinearAlgebra.Projectivization

/-- Request partition and chosen directions for completed requests. -/
structure State (total completed pending dimension width : Nat) where
  /-- Every original request occurs at exactly one completed or pending position. -/
  order : (Fin completed ⊕ Fin pending) ≃ Fin total
  /-- Recovery direction assigned to each completed request. -/
  directions : Fin completed → ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width)

/-- Target tuple in current pending order. -/
def pendingTargets (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin pending) :=
  targets (state.order (.inr request))

/-- Recovery line stored at a completed position. -/
noncomputable def line (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin completed) :=
  puncturedLine (targets (state.order (.inl request))) (state.directions request)

/-- Union of every completed recovery line. -/
noncomputable def occupied (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) :
    Finset (Fin dimension → BinaryExtension width) := by
  classical
  exact Finset.univ.biUnion (line state targets)

/-- The geometric invariant for completed requests. -/
def WellScheduled (state : State total completed pending dimension width)
    (targets : Fin total → Fin dimension → BinaryExtension width) : Prop :=
  Pairwise (fun left right => Disjoint (line state targets left) (line state targets right))

/-- Original data followed by a complete scalar-indexed affine point list. -/
noncomputable def completedRecord (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin completed) :
    Fin (BufferInput.storedWidth requestWidth (2 ^ width) (dimension * width)) → Bool :=
  Fin.append (data (state.order (.inl request)))
    (fun pointBit =>
      let pair := (finProdFinEquiv (m := 2 ^ width) (n := dimension * width)).symm pointBit
      binaryExtensionVectorBits positive
        (PaddedLinePoints.point positive (targets (state.order (.inl request))) (state.directions request) pair.1) pair.2)

/-- Pending records contain only their original request data. -/
def pendingRecord (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool) (request : Fin pending) :=
  data (state.order (.inr request))

/-- The concrete input encoding represented by a scheduler state. -/
noncomputable def input (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) :=
  BufferInput.encode (completedRecord positive state data targets) (pendingRecord state data)

/-- Pending request identities remain distinct in the buffer. -/
theorem pendingRecord_injective (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool) (distinct : Function.Injective data) :
    Function.Injective (pendingRecord state data) := by
  intro left right equal
  exact Sum.inr_injective (state.order.injective (distinct equal))

/-- The original-data projection of a completed record is unchanged. -/
theorem completedRecord_data (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin completed) (bit : Fin requestWidth) :
    completedRecord positive state data targets request (Fin.castAdd (2 ^ width * (dimension * width)) bit) =
      data (state.order (.inl request)) bit := by
  exact Fin.append_left _ _ bit

/-- The point-list projection contains the represented affine-line point. -/
theorem completedRecord_point (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin completed)
    (slot : Fin (2 ^ width)) (bit : Fin (dimension * width)) :
    completedRecord positive state data targets request
      (Fin.natAdd requestWidth (finProdFinEquiv (slot, bit))) =
      binaryExtensionVectorBits positive
        (PaddedLinePoints.point positive (targets (state.order (.inl request))) (state.directions request) slot) bit := by
  simp only [completedRecord, Fin.append_right, Equiv.symm_apply_apply]

/-- The source wires of the buffer expose the represented stored point. -/
theorem pointWire_eval (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin completed)
    (slot : Fin (2 ^ width)) (bit : Fin (dimension * width)) :
    (BufferInput.pointWire pending requestWidth (finProdFinEquiv (request, slot)) bit).eval
      (input positive state data targets) =
      binaryExtensionVectorBits positive
        (PaddedLinePoints.point positive (targets (state.order (.inl request))) (state.directions request) slot) bit := by
  rw [input, BufferInput.pointWire_eval, completedRecord_point]

/-- Reading the pending-data wires gives the original request record. -/
theorem pendingWire_eval (positive : 0 < width)
    (state : State total completed pending dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin pending) (bit : Fin requestWidth) :
    (BufferInput.pendingWire completed (2 ^ width) (dimension * width) request bit).eval
      (input positive state data targets) = data (state.order (.inr request)) bit := by
  rw [input, BufferInput.pendingWire_eval]
  rfl

end Algebraic.MassProduction.Nonuniform.BufferModel
