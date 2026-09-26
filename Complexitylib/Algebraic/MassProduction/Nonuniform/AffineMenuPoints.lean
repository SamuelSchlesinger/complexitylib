/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PaddedLinePoints
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PowerLayout

/-!
# Generating every fixed-menu recovery line

All candidate directions are offline constants. Each point record selects
its request's target bits and adds a precomputed scalar multiple of its
candidate direction. One fixed circuit emits the full power-of-two menu
array, costing at most one gate per point bit.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.AffineMenuPoints

open Sorting
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- Fixed affine offset for each candidate/request/scalar record. -/
noncomputable def offsets (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (index : Fin (networkRecords (menuDepth + requestDepth + width))) : Fin (dimension * width) → Bool :=
  let triple := (PowerLayout.points menuDepth requestDepth width).symm index
  binaryExtensionVectorBits positive
    (PaddedLinePoints.scalarAt positive triple.2.2 • (menu triple.1 triple.2.1).rep)

/-- Every generated point selects the target of its original request. -/
def sources
    (targets : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (index : Fin (networkRecords (menuDepth + requestDepth + width))) :
    Fin (dimension * width) → DeMorgan.Wiring inputs :=
  targets ((PowerLayout.points menuDepth requestDepth width).symm index).2.1

/-- Generate every recovery-line point of every fixed candidate. -/
noncomputable def circuit (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targets : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs) :=
  ConstantTranslations.circuit (offsets positive menu) (sources targets)

/-- `circuit` has exactly the gates of `ConstantTranslations.circuit`; the surrounding wiring adds
none. -/
@[simp] theorem circuit_size
    (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targets :
      Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs) :
    (circuit positive menu targets).size =
      (ConstantTranslations.circuit (offsets positive menu)
          (sources targets)).size := by
  simp [circuit]

/-- Exact field semantics at every fixed candidate/request/scalar output. -/
theorem circuit_eval (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool)
    (targets : Fin (networkRecords requestDepth) → Fin dimension → BinaryExtension width)
    (targetsCorrect : ∀ request bit, (targetWires request bit).eval input =
      binaryExtensionVectorBits positive (targets request) bit)
    (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth))
    (slot : Fin (2 ^ width)) (bit : Fin (dimension * width)) :
    (circuit positive menu targetWires).eval DeMorgan.interpretation input
      (finProdFinEquiv (PowerLayout.points menuDepth requestDepth width (candidate, request, slot), bit)) =
        binaryExtensionVectorBits positive
          (PaddedLinePoints.point positive (targets request) (menu candidate request) slot) bit := by
  rw [circuit, ConstantTranslations.circuit_eval]
  simp only [offsets, sources, Equiv.symm_apply_apply, targetsCorrect]
  exact (PaddedLinePoints.vectorBits_add positive (targets request)
    (PaddedLinePoints.scalarAt positive slot • (menu candidate request).rep) bit).symm

/-- All point generation is linear in the total number of emitted bits. -/
theorem circuit_cost_le (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targets : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs) :
    (circuit positive menu targets).cost DeMorgan.standardCost ≤
      networkRecords (menuDepth + requestDepth + width) * (dimension * width) :=
  ConstantTranslations.circuit_cost_le _ _

end Algebraic.MassProduction.Nonuniform.AffineMenuPoints
