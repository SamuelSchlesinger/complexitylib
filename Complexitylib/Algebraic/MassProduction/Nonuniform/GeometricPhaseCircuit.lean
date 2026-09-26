/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseLayout

/-!
# A complete fixed-menu geometric phase circuit

Generate all affine-line points, retain the original input, evaluate the
menu, and select a clean request prefix. The output retains original
request data and every point of the selected candidate's lines. Correctness
for an encoded occupied state is established separately.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GeometricPhase

open Sorting GeometricPhaseLayout
open scoped LinearAlgebra.Projectivization

set_option backward.isDefEq.respectTransparency false

/-- Evaluate the menu using generated point bits and preserved source data. -/
noncomputable def selector (positive : 0 < width) (menuDepth : Nat)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords (menuDepth + requestDepth + width) + padding =
      networkRecords routingDepth)
    (neededPositive : 0 < needed) (neededFits : needed ≤ networkRecords requestDepth) :=
  MenuSelection.circuit (PowerLayout.points menuDepth requestDepth width) (PowerLayout.codes menuDepth)
    (validWires positive menuDepth requestDepth inputs dimension)
    (keyWires menuDepth requestDepth inputs dimension width)
    (fun source bit => PreparedInputs.original (generatedBits menuDepth requestDepth dimension width)
      (sourceKeys source bit))
    (fun source => PreparedInputs.original (generatedBits menuDepth requestDepth dimension width) (sourceFlags source))
    recordCount (payloadWires menuDepth dimension width original) neededPositive neededFits

/-- `selector` has exactly the gates of `MenuSelection.circuit`; the surrounding wiring adds
none. -/
@[simp] theorem selector_size
    (positive : 0 < width) (menuDepth : Nat)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords (menuDepth + requestDepth + width) + padding =
      networkRecords routingDepth)
    (neededPositive : 0 < needed) (neededFits : needed ≤ networkRecords requestDepth) :
    (selector positive menuDepth sourceKeys sourceFlags original recordCount neededPositive
      neededFits).size =
      (MenuSelection.circuit (PowerLayout.points menuDepth requestDepth width)
          (PowerLayout.codes menuDepth)
          (validWires positive menuDepth requestDepth inputs dimension)
          (keyWires menuDepth requestDepth inputs dimension width)
          (fun source bit =>
            PreparedInputs.original
              (generatedBits menuDepth requestDepth dimension width)
              (sourceKeys source bit))
          (fun source =>
            PreparedInputs.original
              (generatedBits menuDepth requestDepth dimension width)
              (sourceFlags source))
          recordCount (payloadWires menuDepth dimension width original)
          neededPositive neededFits).size := by
  simp [selector]

/-- One complete geometric phase: point generation followed by menu selection. -/
noncomputable def circuit (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords (menuDepth + requestDepth + width) + padding =
      networkRecords routingDepth)
    (neededPositive : 0 < needed) (neededFits : needed ≤ networkRecords requestDepth) :=
  (selector positive menuDepth sourceKeys sourceFlags original recordCount neededPositive neededFits).comp
    (PreparedInputs.circuit (AffineMenuPoints.circuit positive menu targetWires))

/-- The exact gate count of `circuit`. -/
@[simp] theorem circuit_size
    (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords (menuDepth + requestDepth + width) + padding =
      networkRecords routingDepth)
    (neededPositive : 0 < needed) (neededFits : needed ≤ networkRecords requestDepth) :
    (circuit positive menu targetWires sourceKeys sourceFlags original recordCount neededPositive
      neededFits).size =
      (PreparedInputs.circuit
            (AffineMenuPoints.circuit positive menu targetWires)).size +
        (selector positive menuDepth sourceKeys sourceFlags original recordCount
            neededPositive neededFits).size := by
  simp [circuit]

/-- Explicit arithmetic bound for the geometric phase, including point generation. -/
def costBound (menuDepth requestDepth width dimension routingDepth requestWidth : Nat) : Nat :=
  let points := networkRecords (menuDepth + requestDepth + width)
  let addressWidth := dimension * width
  let pointDepth := menuDepth + requestDepth + width
  let payloadWidth := requestWidth + 2 ^ width * addressWidth
  points * addressWidth +
    ((((256 * points * (pointDepth + (menuDepth + (1 + addressWidth)) + 1) ^ 5 +
      128 * networkRecords routingDepth * (routingDepth + addressWidth + 1 + 2) ^ 5) +
      2 * points) + (networkRecords menuDepth * networkRecords requestDepth) * (2 ^ width + 1)) +
      (networkRecords menuDepth *
        (48 * requestDepth * requestDepth * networkRecords requestDepth * (1 + payloadWidth)) +
        48 * menuDepth * menuDepth * networkRecords menuDepth *
          (1 + CandidateSelection.rowBits requestDepth payloadWidth)))

/-- The complete phase has the displayed linear point-count cost bound. -/
theorem circuit_cost_le (positive : 0 < width)
    (menu : Fin (networkRecords menuDepth) → Fin (networkRecords requestDepth) →
      ℙ (BinaryExtension width) (Fin dimension → BinaryExtension width))
    (targetWires : Fin (networkRecords requestDepth) → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceKeys : Fin sources → Fin (dimension * width) → DeMorgan.Wiring inputs)
    (sourceFlags : Fin sources → DeMorgan.Wiring inputs)
    (original : Fin (networkRecords requestDepth) → Fin requestWidth → DeMorgan.Wiring inputs)
    (recordCount : sources + networkRecords (menuDepth + requestDepth + width) + padding =
      networkRecords routingDepth)
    (neededPositive : 0 < needed) (neededFits : needed ≤ networkRecords requestDepth) :
    (circuit positive menu targetWires sourceKeys sourceFlags original recordCount neededPositive neededFits).cost
      DeMorgan.standardCost ≤ costBound menuDepth requestDepth width dimension routingDepth requestWidth := by
  rw [circuit, Circuit.cost_comp, PreparedInputs.circuit_cost]
  apply Nat.add_le_add (AffineMenuPoints.circuit_cost_le positive menu targetWires)
  exact MenuSelection.circuit_cost_le _ _ _ _ _ _ recordCount _ neededPositive neededFits

end Algebraic.MassProduction.Nonuniform.GeometricPhase
