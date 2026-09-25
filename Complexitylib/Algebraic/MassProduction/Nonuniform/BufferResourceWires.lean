/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferLineIncidences
public import Complexitylib.Algebraic.MassProduction.HighRate.ResourceLayout

/-!
# Resource keys and suffix wires from a completed scheduler buffer

Copy and basis-bit metadata remain in each request's original data; the
point address comes from its stored recovery list. These are all fixed wire
selections. Disjoint completed lines imply distinct active resource keys.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferResourceWires

open BufferInput BufferModel

set_option backward.isDefEq.respectTransparency false

/-- Select one original request-data bit from a completed record. -/
def dataWire (slots addressWidth : Nat) (request : Fin total) (bit : Fin requestWidth) :
    DeMorgan.Wiring (inputWidth total 0 requestWidth slots addressWidth) :=
  completedWire 0 request (Fin.castAdd (slots * addressWidth) bit)

/-- The selected bit still belongs to the same original request identity. -/
theorem dataWire_eval (positive : 0 < width)
    (state : State total total 0 dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (request : Fin total) (bit : Fin requestWidth) :
    (dataWire (2 ^ width) (dimension * width) request bit).eval (input positive state data targets) =
      data (state.order (.inl request)) bit := by
  rw [dataWire, input, completedWire_eval, completedRecord_data]

/-- Repeat the stored request's selected payload bits at each scalar slot. -/
def payload (width dimension : Nat) (projection : Fin payloadWidth → Fin requestWidth)
    (incidence : Fin (total * 2 ^ width)) (bit : Fin payloadWidth) :
    DeMorgan.Wiring (inputWidth total 0 requestWidth (2 ^ width) (dimension * width)) :=
  dataWire (2 ^ width) (dimension * width)
    ((finProdFinEquiv (m := total) (n := 2 ^ width)).symm incidence).1 (projection bit)

/-- Repeated payload wires read the original data at the completed request's identity. -/
theorem payload_eval (positive : 0 < width)
    (state : State total total 0 dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width)
    (projection : Fin payloadWidth → Fin requestWidth) (request : Fin total) (slot : Fin (2 ^ width)) (bit : Fin payloadWidth) :
    (payload width dimension projection (finProdFinEquiv (request, slot)) bit).eval
      (input positive state data targets) = data (state.order (.inl request)) (projection bit) := by
  simp only [payload, Equiv.symm_apply_apply, dataWire_eval]

/-- Resource key: preserved copy metadata, stored point, preserved basis-bit metadata. -/
def keys (width dimension : Nat)
    (copyProjection : Fin copyBits → Fin requestWidth)
    (selectorProjection : Fin selectorBits → Fin requestWidth)
    (incidence : Fin (total * 2 ^ width)) :
    Fin (HighRate.ResourceLayout.keyWidth copyBits dimension width selectorBits) →
      DeMorgan.Wiring (inputWidth total 0 requestWidth (2 ^ width) (dimension * width)) :=
  Fin.append (payload width dimension copyProjection incidence)
    (Fin.append (pointWire 0 requestWidth incidence) (payload width dimension selectorProjection incidence))

/-- Reading a resource key's point field gives exactly its stored point. -/
theorem keys_point_eval (positive : 0 < width)
    (state : State total total 0 dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width)
    (copyProjection : Fin copyBits → Fin requestWidth)
    (selectorProjection : Fin selectorBits → Fin requestWidth)
    (incidence : Fin (total * 2 ^ width)) (bit : Fin (dimension * width)) :
    (keys width dimension copyProjection selectorProjection incidence
      (Fin.natAdd copyBits (Fin.castAdd selectorBits bit))).eval (input positive state data targets) =
      binaryExtensionVectorBits positive (incidencePoint positive state targets incidence) bit := by
  obtain ⟨⟨request, slot⟩, rfl⟩ := finProdFinEquiv.surjective incidence
  simp only [keys, Fin.append_right, Fin.append_left, BufferModel.pointWire_eval,
    incidencePoint, Equiv.symm_apply_apply]

/-- Every completed incidence key matches the exact resource-bank position
described by the preserved request metadata and stored geometric point. -/
theorem keys_eval (positive : 0 < width)
    (state : State total total 0 dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width)
    (copyProjection : Fin copyBits → Fin requestWidth)
    (selectorProjection : Fin selectorBits → Fin requestWidth)
    (copiesAt : Fin total → Fin copies) (selectorsAt : Fin total → Fin width)
    (copyCorrect : ∀ request bit, data request (copyProjection bit) = finiteIndexBits copyBits (copiesAt request) bit)
    (selectorCorrect : ∀ request bit, data request (selectorProjection bit) =
      finiteIndexBits selectorBits (selectorsAt request) bit)
    (request : Fin total) (slot : Fin (2 ^ width)) :
    (fun bit => (keys width dimension copyProjection selectorProjection (finProdFinEquiv (request, slot)) bit).eval
      (input positive state data targets)) =
      HighRate.ResourceLayout.key copyBits selectorBits
        (HighRate.ResourceLayout.position positive (copiesAt (state.order (.inl request)))
          (PaddedLinePoints.point positive (targets (state.order (.inl request))) (state.directions request) slot)
          (selectorsAt (state.order (.inl request)))) := by
  rw [HighRate.ResourceLayout.key_position]
  funext bit
  refine Fin.addCases (fun copyBit => ?_) (fun restBit => ?_) bit
  · simp only [keys, Fin.append_left, payload_eval, copyCorrect]
  · refine Fin.addCases (fun pointBit => ?_) (fun selectorBit => ?_) restBit
    · simp only [keys, Fin.append_right, Fin.append_left, BufferModel.pointWire_eval]
    · simp only [keys, Fin.append_right, payload_eval, selectorCorrect]

/-- Completed-buffer disjointness discharges the scatter uniqueness premise. -/
theorem activeKeys_injective (positive : 0 < width)
    (state : State total total 0 dimension width)
    (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width) (scheduled : WellScheduled state targets)
    (copyProjection : Fin copyBits → Fin requestWidth)
    (selectorProjection : Fin selectorBits → Fin requestWidth)
    (left right : Fin (total * 2 ^ width))
    (leftActive : incidenceValid positive left = true) (rightActive : incidenceValid positive right = true)
    (sameKey : (fun bit => (keys width dimension copyProjection selectorProjection left bit).eval
        (input positive state data targets)) =
      (fun bit => (keys width dimension copyProjection selectorProjection right bit).eval
        (input positive state data targets))) : left = right := by
  apply incidencePoint_injective positive state targets scheduled left right leftActive rightActive
  apply binaryExtensionVectorBits_injective positive
  funext bit
  have equal := congrFun sameKey (Fin.natAdd copyBits (Fin.castAdd selectorBits bit))
  simpa only [keys_point_eval] using equal

end Algebraic.MassProduction.Nonuniform.BufferResourceWires
