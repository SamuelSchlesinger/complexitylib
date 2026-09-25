/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.AffineMenuPoints
public import Complexitylib.Algebraic.MassProduction.Nonuniform.PreparedInputs
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MenuSelection

/-!
# Wiring the geometric phase evaluator

The generated point block precedes the original input. Constant validity
flags discard the zero scalar. Each request payload carries both its
original data and the complete generated point list of that candidate, so
accepted point lists can become occupancy inputs in the next phase.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GeometricPhaseLayout

open Sorting
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- Total width of the generated point block. -/
abbrev generatedBits (menuDepth requestDepth dimension width : Nat) : Nat :=
  networkRecords (menuDepth + requestDepth + width) * (dimension * width)

/-- Constant scalar-validity flags for every menu point. -/
noncomputable def validWires (positive : 0 < width) (menuDepth requestDepth inputs dimension : Nat)
    (index : Fin (networkRecords (menuDepth + requestDepth + width))) :
    DeMorgan.Wiring (generatedBits menuDepth requestDepth dimension width + inputs) :=
  .constant (PaddedLinePoints.valid positive
    ((PowerLayout.points menuDepth requestDepth width).symm index).2.2)

/-- The point address of a generated record. -/
def keyWires (menuDepth requestDepth inputs dimension width : Nat)
    (index : Fin (networkRecords (menuDepth + requestDepth + width))) (bit : Fin (dimension * width)) :
    DeMorgan.Wiring (generatedBits menuDepth requestDepth dimension width + inputs) :=
  PreparedInputs.output inputs (finProdFinEquiv (index, bit))

/-- Carry original request data followed by all candidate-specific point bits. -/
def payloadWires (menuDepth dimension width : Nat)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (line : Fin (networkRecords menuDepth * networkRecords requestDepth)) :
    Fin (requestWidth + 2 ^ width * (dimension * width)) →
      DeMorgan.Wiring (generatedBits menuDepth requestDepth dimension width + inputs) :=
  let pair := (finProdFinEquiv (m := networkRecords menuDepth) (n := networkRecords requestDepth)).symm line
  Fin.append
    (fun bit => PreparedInputs.original (generatedBits menuDepth requestDepth dimension width)
      (original pair.2 bit))
    (fun pointBit =>
      let slotAndBit := (finProdFinEquiv (m := 2 ^ width) (n := dimension * width)).symm pointBit
      keyWires menuDepth requestDepth inputs dimension width
        (PowerLayout.points menuDepth requestDepth width (pair.1, pair.2, slotAndBit.1)) slotAndBit.2)

/-- Padded validity is preserved at the corresponding triple index. -/
theorem validWires_eval (positive : 0 < width)
    (prepared : Fin (generatedBits menuDepth requestDepth dimension width + inputs) → Bool)
    (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth))
    (slot : Fin (2 ^ width)) :
    (validWires positive menuDepth requestDepth inputs dimension
      (PowerLayout.points menuDepth requestDepth width (candidate, request, slot))).eval prepared =
        PaddedLinePoints.valid positive slot := by
  simp only [validWires, Equiv.symm_apply_apply, DeMorgan.Wiring.eval_constant]

/-- Generated point keys have the exact field-level affine-line semantics. -/
theorem keyWires_eval (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool)
    (targets : Fin (networkRecords requestDepth) → Fin dimension → BinaryExtension width)
    (targetsCorrect : ∀ request bit, (targetWires request bit).eval input =
      binaryExtensionVectorBits positive (targets request) bit)
    (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth))
    (slot : Fin (2 ^ width)) (bit : Fin (dimension * width)) :
    (keyWires menuDepth requestDepth inputs dimension width
      (PowerLayout.points menuDepth requestDepth width (candidate, request, slot)) bit).eval
      ((PreparedInputs.circuit (AffineMenuPoints.circuit positive menu targetWires)).eval
        DeMorgan.interpretation input) =
      binaryExtensionVectorBits positive
        (PaddedLinePoints.point positive (targets request) (menu candidate request) slot) bit := by
  rw [keyWires, PreparedInputs.output_eval]
  exact AffineMenuPoints.circuit_eval positive menu targetWires input targets targetsCorrect candidate request slot bit

/-- The set tested by the menu evaluator is precisely the encoded punctured line. -/
theorem requestSet_eq (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool)
    (targets : Fin (networkRecords requestDepth) → Fin dimension → BinaryExtension width)
    (targetsCorrect : ∀ request bit, (targetWires request bit).eval input =
      binaryExtensionVectorBits positive (targets request) bit)
    (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth)) :
    MenuSelection.requestSet (PowerLayout.points menuDepth requestDepth width)
      (validWires positive menuDepth requestDepth inputs dimension)
      (keyWires menuDepth requestDepth inputs dimension width)
      ((PreparedInputs.circuit (AffineMenuPoints.circuit positive menu targetWires)).eval
        DeMorgan.interpretation input) candidate request =
      (puncturedLine (targets request) (menu candidate request)).image (binaryExtensionVectorBits positive) := by
  unfold MenuSelection.requestSet
  simp_rw [validWires_eval, keyWires_eval positive menu targetWires input targets targetsCorrect]
  exact PaddedLinePoints.pointSet_eq positive (targets request) (menu candidate request)

/-- Original request data is carried without modification. -/
theorem payloadWires_original_eval
    (generated : Circuit DeMorgan.signature inputs gates (generatedBits menuDepth requestDepth dimension width))
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool) (candidate : Fin (networkRecords menuDepth))
    (request : Fin (networkRecords requestDepth)) (bit : Fin requestWidth) :
    (payloadWires menuDepth dimension width original (finProdFinEquiv (candidate, request))
      (Fin.castAdd (2 ^ width * (dimension * width)) bit)).eval
      ((PreparedInputs.circuit generated).eval DeMorgan.interpretation input) =
        (original request bit).eval input := by
  simp only [payloadWires, Equiv.symm_apply_apply, Fin.append_left, PreparedInputs.original_eval]

/-- The point-list suffix of a request payload carries the generated keys. -/
theorem payloadWires_point_eval
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (prepared : Fin (generatedBits menuDepth requestDepth dimension width + inputs) → Bool)
    (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth))
    (slot : Fin (2 ^ width)) (bit : Fin (dimension * width)) :
    (payloadWires menuDepth dimension width original (finProdFinEquiv (candidate, request))
      (Fin.natAdd requestWidth (finProdFinEquiv (slot, bit)))).eval prepared =
      (keyWires menuDepth requestDepth inputs dimension width
        (PowerLayout.points menuDepth requestDepth width (candidate, request, slot)) bit).eval prepared := by
  simp only [payloadWires, Equiv.symm_apply_apply, Fin.append_right]

/-- Lifting source wires past preprocessing preserves their occupied set. -/
theorem occupied_prepared
    (generated : Circuit DeMorgan.signature inputs gates outputs)
    (sourceKeys : Fin sources → Fin keyWidth → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs) (input : Fin inputs → Bool) :
    MenuPointLayout.occupied
      (fun source bit => PreparedInputs.original outputs (sourceKeys source bit))
      (fun source => PreparedInputs.original outputs (sourceFlags source))
      ((PreparedInputs.circuit generated).eval DeMorgan.interpretation input) =
        MenuPointLayout.occupied sourceKeys sourceFlags input := by
  simp only [MenuPointLayout.occupied, PreparedInputs.original_eval]

/-- The evaluator's encoded cleanliness predicate is exactly geometric cleanliness. -/
theorem requestClean_iff (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (input : Fin inputs → Bool)
    (targets : Fin (networkRecords requestDepth) → Fin dimension → BinaryExtension width)
    (targetsCorrect : ∀ request bit, (targetWires request bit).eval input =
      binaryExtensionVectorBits positive (targets request) bit)
    (occupied : Finset (Fin dimension → BinaryExtension width))
    (occupiedCorrect : MenuPointLayout.occupied sourceKeys sourceFlags input =
      occupied.image (binaryExtensionVectorBits positive))
    (candidate : Fin (networkRecords menuDepth)) (request : Fin (networkRecords requestDepth)) :
    MenuSelection.RequestClean (PowerLayout.points menuDepth requestDepth width)
      (validWires positive menuDepth requestDepth inputs dimension)
      (keyWires menuDepth requestDepth inputs dimension width)
      (fun source bit => PreparedInputs.original (generatedBits menuDepth requestDepth dimension width)
        (sourceKeys source bit))
      (fun source => PreparedInputs.original (generatedBits menuDepth requestDepth dimension width)
        (sourceFlags source))
      ((PreparedInputs.circuit (AffineMenuPoints.circuit positive menu targetWires)).eval
        DeMorgan.interpretation input) candidate request ↔
      Clean (fun request direction => puncturedLine (targets request) direction)
        occupied (menu candidate) request := by
  unfold MenuSelection.RequestClean Clean
  simp_rw [requestSet_eq positive menu targetWires input targets targetsCorrect]
  rw [occupied_prepared, occupiedCorrect]
  simp only [Finset.disjoint_image (binaryExtensionVectorBits_injective positive)]

end Algebraic.MassProduction.Nonuniform.GeometricPhaseLayout
