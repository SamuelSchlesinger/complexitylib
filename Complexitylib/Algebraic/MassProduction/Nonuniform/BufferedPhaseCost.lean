/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferedPhase
public import Complexitylib.Algebraic.MassProduction.Nonuniform.GeometricPhaseCost

/-!
# Uniform cost bounds over the buffer phases

All phase depths are bounded using the logarithm of the original request
count. The resulting bound is linear in `total * 2^width`; all remaining
factors are polynomial in bit widths and logarithms.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferedPhase

open Sorting

private theorem linear_le_power (address : Nat) : 2 + 3 * address ≤ 2 ^ (address + 2) := by
  induction address with
  | zero => norm_num
  | succ address inductionHypothesis =>
      rw [show address + 1 + 2 = (address + 2) + 1 by omega, pow_succ]
      have positive : 1 ≤ 2 ^ address := Nat.one_le_pow _ _ (by omega)
      have power : 2 ^ (address + 2) = 4 * 2 ^ address := by rw [pow_add]; ring
      nlinarith

/-- A uniform bound on the polynomial parameters of every phase. -/
def height (total dimension width requestWidth : Nat) : Nat :=
  5 * FiniteParameters.binaryDepth total + 4 * (dimension * width) + 2 * width + requestWidth + 10

/-- Every active sorting depth is at most the original batch's ceiling logarithm. -/
theorem requestDepth_le (activeLe : networkRecords requestDepth ≤ total) :
    requestDepth ≤ FiniteParameters.binaryDepth total := by
  have powers := activeLe.trans (FiniteParameters.records_le_networkRecords total)
  simpa only [networkRecords_eq_two_pow, Nat.pow_le_pow_iff_right (by omega : 1 < 2)] using powers

/-- The menu depth adds at most the geometric address width and two bits. -/
theorem menuDepth_le (activeLe : networkRecords requestDepth ≤ total) :
    menuDepth total requestDepth dimension width ≤
      FiniteParameters.binaryDepth total + dimension * width + 2 := by
  have totalPositive : 1 ≤ total := by
    have activePositive : 0 < networkRecords requestDepth := by simp
    omega
  have totalFits : total ≤ 2 ^ FiniteParameters.binaryDepth total := by
    simpa only [networkRecords_eq_two_pow] using FiniteParameters.records_le_networkRecords total
  apply FiniteParameters.binaryDepth_le
  calc
    _ ≤ total * (1 + 3 * (dimension * width)) + 1 := Nat.add_le_add_right (Nat.div_le_self _ _) _
    _ ≤ total * (2 + 3 * (dimension * width)) := by nlinarith
    _ ≤ 2 ^ FiniteParameters.binaryDepth total * 2 ^ (dimension * width + 2) :=
      Nat.mul_le_mul totalFits (linear_le_power _)
    _ = _ := by rw [← pow_add, Nat.add_assoc]

/-- Canonical occupancy routing has logarithmic depth in the original point budget. -/
theorem routingDepth_le (completedLe : completed ≤ total) (activeLe : networkRecords requestDepth ≤ total) :
    routingDepth total completed requestDepth dimension width ≤
      2 * FiniteParameters.binaryDepth total + dimension * width + width + 3 := by
  let depth := FiniteParameters.binaryDepth total
  have menuBound := menuDepth_le (dimension := dimension) (width := width) activeLe
  have requestBound := requestDepth_le activeLe
  have totalFits : total ≤ 2 ^ depth := by
    simpa only [networkRecords_eq_two_pow] using FiniteParameters.records_le_networkRecords total
  have oldBound : completed * 2 ^ width ≤ 2 ^ (2 * depth + dimension * width + width + 2) := by
    calc
      _ ≤ 2 ^ depth * 2 ^ width := Nat.mul_le_mul_right _ (completedLe.trans totalFits)
      _ = 2 ^ (depth + width) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have pointBound : networkRecords (menuDepth total requestDepth dimension width + requestDepth + width) ≤
      2 ^ (2 * depth + dimension * width + width + 2) := by
    rw [networkRecords_eq_two_pow]
    apply Nat.pow_le_pow_right (by omega)
    dsimp [depth] at *
    omega
  apply FiniteParameters.binaryDepth_le
  change completed * 2 ^ width + networkRecords (menuDepth total requestDepth dimension width + requestDepth + width) ≤ _
  calc
    _ ≤ 2 ^ (2 * depth + dimension * width + width + 2) +
        2 ^ (2 * depth + dimension * width + width + 2) := Nat.add_le_add oldBound pointBound
    _ = _ := by rw [show 2 * depth + dimension * width + width + 3 =
      (2 * depth + dimension * width + width + 2) + 1 by omega, pow_succ]; ring

/-- Every generated point array is linear in the original number of requests. -/
theorem pointCount_le (activeLe : networkRecords requestDepth ≤ total) :
    networkRecords (menuDepth total requestDepth dimension width + requestDepth + width) ≤
      2 * (total * (2 + 3 * (dimension * width))) * 2 ^ width := by
  have candidates := powerPhaseMenuCandidateCount_le total (networkRecords requestDepth) (dimension * width) activeLe
  calc
    _ = networkRecords (menuDepth total requestDepth dimension width) * networkRecords requestDepth * 2 ^ width := by
      simp only [networkRecords_eq_two_pow, pow_add]
    _ ≤ _ := Nat.mul_le_mul_right _ candidates

/-- The combined generated and padded occupancy arrays remain linear. -/
theorem pointAndRoutingCount_le (completedLe : completed ≤ total) (activeLe : networkRecords requestDepth ≤ total) :
    networkRecords (menuDepth total requestDepth dimension width + requestDepth + width) +
      networkRecords (routingDepth total completed requestDepth dimension width) ≤
        total * 2 ^ width * (14 + 18 * (dimension * width)) := by
  have pointBound := pointCount_le (dimension := dimension) (width := width) activeLe
  have oldBound := Nat.mul_le_mul_right (2 ^ width) completedLe
  have positive : 0 < routingRecords total completed requestDepth dimension width := by
    have pointPositive : 0 < networkRecords (menuDepth total requestDepth dimension width + requestDepth + width) := by simp
    unfold routingRecords
    omega
  have routed := (FiniteParameters.networkRecords_binaryDepth_lt_two_mul _ positive).le
  change networkRecords (routingDepth total completed requestDepth dimension width) ≤
    2 * (completed * 2 ^ width + networkRecords (menuDepth total requestDepth dimension width + requestDepth + width)) at routed
  nlinarith

/-- One compacted phase has a cost linear in the original point budget,
with a fixed polynomial factor independent of the active request count. -/
theorem costBound_le (completedLe : completed ≤ total) (activeLe : networkRecords requestDepth ≤ total) :
    costBound total completed requestDepth dimension width requestWidth ≤
      10000 * (total * 2 ^ width * (14 + 18 * (dimension * width))) *
        height total dimension width requestWidth ^ 5 := by
  have menuBound := menuDepth_le (dimension := dimension) (width := width) activeLe
  have requestBound := requestDepth_le activeLe
  have routingBound := routingDepth_le (dimension := dimension) (width := width) completedLe activeLe
  have heightBound : 2 * menuDepth total requestDepth dimension width + requestDepth + width + dimension * width +
      routingDepth total completed requestDepth dimension width + requestWidth + 3 ≤
        height total dimension width requestWidth := by
    dsimp [height]
    omega
  exact (GeometricPhase.costBound_le_linear heightBound).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (pointAndRoutingCount_le completedLe activeLe)))

end Algebraic.MassProduction.Nonuniform.BufferedPhase
