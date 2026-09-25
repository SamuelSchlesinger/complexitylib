/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BatchRouting

/-!
# A compact shared-router size bound

The two sorting passes and shared propagation scan cost a linear number of
records times a fixed polynomial in key width, value width, and sorting depth.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.Broadcast

open Sorting RoutingMetadata

/-- A compact polynomial bound retaining linear dependence on record count. -/
theorem routingCircuit_cost_le_polynomial :
    (routingCircuit depth keyWidth (depth + 1) valueWidth).cost DeMorgan.standardCost ≤
      128 * networkRecords depth * (depth + keyWidth + valueWidth + 2) ^ 5 := by
  let width := depth + keyWidth + valueWidth + 2
  have widthPositive : 1 ≤ width := by dsimp [width]; omega
  have depthLe : depth ≤ width := by dsimp [width]; omega
  have valueLe : valueWidth ≤ width := by dsimp [width]; omega
  have keyLe : keyWidth ≤ width := by dsimp [width]; omega
  have recordLe : recordWidth keyWidth (depth + 1) valueWidth ≤ width := by
    dsimp [recordWidth, Routing.recordWidth, width]
    omega
  have sorterBound (key : Nat) (keyLe : key ≤ width) :
      depth * depth * networkRecords depth *
        ((2 * recordWidth keyWidth (depth + 1) valueWidth) *
          (2 * (key * (6 * key + 4)) + 4)) ≤
        48 * networkRecords depth * width ^ 5 := by
    calc
      _ ≤ width * width * networkRecords depth *
          ((2 * width) * (2 * (width * (6 * width + 4)) + 4)) := by gcongr
      _ ≤ width * width * networkRecords depth * ((2 * width) * (24 * width ^ 2)) := by
        gcongr
        nlinarith
      _ = _ := by ring
  have firstSort := sorterBound (keyWidth + 1) (by dsimp [width]; omega)
  have lastSort := sorterBound (depth + 2) (by dsimp [width]; omega)
  have scan : networkRecords depth * (valueWidth * (6 * keyWidth + 4)) ≤
      10 * networkRecords depth * width ^ 2 := by
    calc
      _ ≤ networkRecords depth * (width * (6 * width + 4)) := by gcongr
      _ ≤ 10 * networkRecords depth * width ^ 2 := by
        have localBound : width * (6 * width + 4) ≤ 10 * width ^ 2 := by nlinarith
        nlinarith [Nat.mul_le_mul_left (networkRecords depth) localBound]
  have wiring : networkBits depth (recordWidth keyWidth (depth + 1) valueWidth) ≤
      networkRecords depth * width := Nat.mul_le_mul_left _ recordLe
  have squareLe : width ^ 2 ≤ width ^ 5 := Nat.pow_le_pow_right widthPositive (by decide)
  have linearLe : width ≤ width ^ 5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right widthPositive (by decide : 1 ≤ 5)
  have scanLarge := scan.trans (Nat.mul_le_mul_left (10 * networkRecords depth) squareLe)
  have wiringLarge := wiring.trans (Nat.mul_le_mul_left (networkRecords depth) linearLe)
  have raw := routingCircuit_cost_le (depth := depth) (keyWidth := keyWidth)
    (metadataWidth := depth + 1) (valueWidth := valueWidth)
  change _ ≤ 128 * networkRecords depth * width ^ 5
  calc
    _ ≤ (48 * networkRecords depth * width ^ 5 + 10 * networkRecords depth * width ^ 5) +
        (networkRecords depth * width ^ 5 + 48 * networkRecords depth * width ^ 5) :=
      raw.trans (Nat.add_le_add (Nat.add_le_add firstSort scanLarge)
        (Nat.add_le_add wiringLarge lastSort))
    _ ≤ _ := by nlinarith

end Algebraic.MassProduction.Nonuniform.Broadcast
