/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseCircuit

/-!
# A linear point-count bound for a geometric phase

The polynomial factor contains only depths and scalar bit widths. In
particular, the full `2^width` point list is charged once, rather than being
raised to a power as part of a record-width estimate.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.GeometricPhase

open Sorting

set_option maxHeartbeats 600000

/-- A phase is linear in generated and routed point counts, with a fifth
degree polynomial in its bit widths and sorting depths. -/
theorem costBound_le_linear
    (heightBound : 2 * menuDepth + requestDepth + width + dimension * width +
      routingDepth + requestWidth + 3 ≤ height) :
    costBound menuDepth requestDepth width dimension routingDepth requestWidth ≤
      10000 * (networkRecords (menuDepth + requestDepth + width) + networkRecords routingDepth) * height ^ 5 := by
  let points := networkRecords (menuDepth + requestDepth + width)
  let address := dimension * width
  let q := 2 ^ width
  let rows := networkRecords requestDepth
  let candidates := networkRecords menuDepth
  have pointCount : points = candidates * rows * q := by
    simp only [points, candidates, rows, q, networkRecords_eq_two_pow, pow_add]
  have qPositive : 1 ≤ q := Nat.one_le_pow _ _ (by omega)
  have rowsPositive : 1 ≤ rows := by
    simpa only [rows, networkRecords_eq_two_pow] using
      (Nat.one_le_pow requestDepth 2 (by omega))
  have heightPositive : 1 ≤ height := by omega
  have heightPower : 1 ≤ height ^ 5 := Nat.one_le_pow _ _ heightPositive
  have firstPower : height ≤ height ^ 5 := by
    simpa using Nat.pow_le_pow_right heightPositive (show 1 ≤ 5 by omega)
  have thirdPower : height ^ 3 ≤ height ^ 5 :=
    Nat.pow_le_pow_right heightPositive (by omega)
  have addressBound : address ≤ height := by dsimp [address]; omega
  have payloadBound : 1 + requestWidth + q * address ≤ q * height := by
    have small : 1 + requestWidth + address ≤ height := by dsimp [address]; omega
    nlinarith
  have rowBound : 1 + rows * (1 + (requestWidth + q * address)) ≤ 2 * rows * q * height := by
    have productPositive : 1 ≤ rows * q * height := by
      exact Nat.mul_le_mul (Nat.mul_le_mul rowsPositive qPositive) heightPositive
    have scaled := Nat.mul_le_mul_left rows payloadBound
    nlinarith
  have generated : points * address ≤ points * height ^ 5 :=
    Nat.mul_le_mul_left _ (addressBound.trans firstPower)
  have duplicateCost : 256 * points *
      (menuDepth + requestDepth + width + (menuDepth + (1 + address)) + 1) ^ 5 ≤
        8192 * (points * height ^ 5) := by
    calc
      _ ≤ 256 * points * (2 * height) ^ 5 := by gcongr; dsimp [address]; omega
      _ = _ := by ring
  have routed : 128 * networkRecords routingDepth * (routingDepth + address + 1 + 2) ^ 5 ≤
      128 * (networkRecords routingDepth * height ^ 5) := by
    calc
      _ ≤ 128 * networkRecords routingDepth * height ^ 5 := by gcongr; dsimp [address]; omega
      _ = _ := by ring
  have marked : 2 * points ≤ 2 * (points * height ^ 5) := by nlinarith
  have grouped : candidates * rows * (q + 1) ≤ 2 * (points * height ^ 5) := by
    calc
      _ ≤ candidates * rows * (2 * q) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * points := by rw [pointCount]; ring
      _ ≤ _ := marked
  have inner : candidates * (48 * requestDepth * requestDepth * rows *
      (1 + (requestWidth + q * address))) ≤ 48 * (points * height ^ 5) := by
    calc
      _ ≤ candidates * (48 * height * height * rows * (q * height)) := by
        gcongr
        · omega
        · omega
        · simpa only [Nat.add_assoc] using payloadBound
      _ = 48 * points * height ^ 3 := by rw [pointCount]; ring
      _ ≤ 48 * points * height ^ 5 := Nat.mul_le_mul_left _ thirdPower
      _ = _ := by ring
  have outer : 48 * menuDepth * menuDepth * candidates *
      (1 + rows * (1 + (requestWidth + q * address))) ≤ 96 * (points * height ^ 5) := by
    calc
      _ ≤ 48 * height * height * candidates * (2 * rows * q * height) := by
        gcongr
        · omega
        · omega
      _ = 96 * points * height ^ 3 := by rw [pointCount]; ring
      _ ≤ 96 * points * height ^ 5 := Nat.mul_le_mul_left _ thirdPower
      _ = _ := by ring
  change points * address +
    ((((256 * points * (menuDepth + requestDepth + width + (menuDepth + (1 + address)) + 1) ^ 5 +
      128 * networkRecords routingDepth * (routingDepth + address + 1 + 2) ^ 5) + 2 * points) +
      candidates * rows * (q + 1)) +
      (candidates * (48 * requestDepth * requestDepth * rows * (1 + (requestWidth + q * address))) +
      48 * menuDepth * menuDepth * candidates * (1 + rows * (1 + (requestWidth + q * address))))) ≤ _
  calc
    _ ≤ 8341 * (points * height ^ 5) + 128 * (networkRecords routingDepth * height ^ 5) := by omega
    _ ≤ 10000 * (points * height ^ 5) + 10000 * (networkRecords routingDepth * height ^ 5) := by omega
    _ = 10000 * (points + networkRecords routingDepth) * height ^ 5 := by ring

end Algebraic.MassProduction.Nonuniform.GeometricPhase
