/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.UhligRecursion

/-!
# Parameters for Uhlig mass production

This module chooses the logarithmic prefix width used by the sharp theorem
and proves an explicit polynomial bound for the overhead of one recursive
Uhlig layer.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace UhligTheorem

open UhligCircuit
open UhligRecursion

/-- We spend twice the binary logarithm of the ambient input length per
two-copy layer.  This makes the ordinary resource population at least the
ambient input length while still costing only `O(log n)` variables per
layer. -/
def uhligPrefixWidth (inputs : Nat) : Nat :=
  2 * Nat.log 2 inputs

/-- Inputs left for the terminal one-copy synthesis. -/
def uhligBaseWidth (depth inputs : Nat) : Nat :=
  inputs - depth * uhligPrefixWidth inputs

theorem two_pow_uhligPrefixWidth_le_square
    (inputs : Nat) (inputsPositive : 0 < inputs) :
    2 ^ uhligPrefixWidth inputs <= inputs ^ 2 := by
  unfold uhligPrefixWidth
  rw [Nat.mul_comm 2, pow_mul]
  exact Nat.pow_le_pow_left
    (Nat.pow_log_le_self 2 (Nat.ne_of_gt inputsPositive)) 2

theorem input_le_two_pow_uhligPrefixWidth
    (inputs : Nat) (inputsLarge : 2 <= inputs) :
    inputs <= 2 ^ uhligPrefixWidth inputs := by
  let logarithmicPower := 2 ^ Nat.log 2 inputs
  have logarithmicPowerAtLeastTwo : 2 <= logarithmicPower := by
    have logPositive : 0 < Nat.log 2 inputs :=
      Nat.log_pos (by omega) inputsLarge
    dsimp [logarithmicPower]
    exact Nat.one_lt_two_pow_iff.mpr (Nat.ne_of_gt logPositive)
  have inputBelowDouble :
      inputs < logarithmicPower * 2 := by
    have bound := Nat.lt_pow_succ_log_self (by omega : 1 < 2) inputs
    simpa only [pow_succ, logarithmicPower, Nat.mul_comm] using bound
  calc
    inputs <= logarithmicPower * 2 := Nat.le_of_lt inputBelowDouble
    _ <= logarithmicPower * logarithmicPower := by gcongr
    _ = 2 ^ uhligPrefixWidth inputs := by
      unfold uhligPrefixWidth logarithmicPower
      rw [Nat.mul_comm 2, pow_mul, pow_two]

theorem uhligPrefixWidth_le_twice
    (inputs : Nat) :
    uhligPrefixWidth inputs <= 2 * inputs := by
  unfold uhligPrefixWidth
  exact Nat.mul_le_mul_left 2 (Nat.log_le_self 2 inputs)

/-- Expanded polynomial for the cost of one pair-factored Uhlig layer. -/
theorem layerOverheadEnvelope_eq
    (prefixWidth suffixWidth : Nat) :
    layerOverheadEnvelope prefixWidth suffixWidth =
      let sources := 2 ^ prefixWidth
      let resources := sources + 1
      resources *
          (suffixWidth *
            (2 * sources * resources * (prefixWidth + 1))) +
        2 *
          (sources *
              (sources *
                  (4 * prefixWidth + 4 * resources + 2) +
                sources) +
            sources) := by
  have sourceCount := prefixCount_eq prefixWidth
  have resourceCountIdentity := resourceCount_eq prefixWidth
  unfold layerOverheadEnvelope routedSuffixCostBound
    sharedDecodedCostBound candidateRowCostBound candidateDecodedCostBound
  unfold resourceCount at resourceCountIdentity
  simp only
  rw [resourceCount_eq, sourceCount, resourceCountIdentity]
  ring

/-- With the chosen logarithmic prefix, the entire pair-factored layer
overhead is bounded by a fixed degree-eight monomial. -/
theorem layerOverheadEnvelope_uhligPrefixWidth_le
    (inputs : Nat) (inputsLarge : 2 <= inputs) :
    layerOverheadEnvelope (uhligPrefixWidth inputs) inputs <=
      64 * inputs ^ 8 := by
  let prefixWidth := uhligPrefixWidth inputs
  let sources := 2 ^ prefixWidth
  let resources := sources + 1
  have inputsPositive : 0 < inputs := by omega
  have squarePositive : 0 < inputs ^ 2 := pow_pos inputsPositive 2
  have sourcesBound : sources <= inputs ^ 2 := by
    dsimp [sources, prefixWidth]
    exact two_pow_uhligPrefixWidth_le_square inputs inputsPositive
  have resourcesBound : resources <= 2 * inputs ^ 2 := by
    dsimp [resources]
    calc
      sources + 1 <= inputs ^ 2 + 1 := Nat.add_le_add_right sourcesBound 1
      _ <= 2 * inputs ^ 2 := by omega
  have prefixBound : prefixWidth <= 2 * inputs := by
    dsimp [prefixWidth]
    exact uhligPrefixWidth_le_twice inputs
  have prefixSuccessorBound : prefixWidth + 1 <= 3 * inputs := by omega
  have routedBound :
      2 * sources * resources * (prefixWidth + 1) <=
        12 * inputs ^ 5 := by
    calc
      2 * sources * resources * (prefixWidth + 1) <=
          2 * inputs ^ 2 * (2 * inputs ^ 2) * (3 * inputs) := by
        gcongr
      _ = 12 * inputs ^ 5 := by ring
  have candidateBound :
      4 * prefixWidth + 4 * resources + 2 <= 18 * inputs ^ 2 := by
    have inputLeSquare : inputs <= inputs ^ 2 := by
      simpa only [pow_two] using Nat.le_mul_of_pos_left inputs inputsPositive
    calc
      4 * prefixWidth + 4 * resources + 2 <=
          4 * (2 * inputs) + 4 * (2 * inputs ^ 2) + 2 := by gcongr
      _ <= 18 * inputs ^ 2 := by omega
  have squareLeSixth : inputs ^ 2 <= inputs ^ 6 :=
    Nat.pow_le_pow_right inputsPositive (by omega)
  have fourthLeSixth : inputs ^ 4 <= inputs ^ 6 :=
    Nat.pow_le_pow_right inputsPositive (by omega)
  have decodedBound :
      sources * (sources *
          (4 * prefixWidth + 4 * resources + 2) + sources) + sources <=
        20 * inputs ^ 6 := by
    calc
      sources * (sources *
            (4 * prefixWidth + 4 * resources + 2) + sources) + sources <=
          inputs ^ 2 *
              (inputs ^ 2 * (18 * inputs ^ 2) + inputs ^ 2) +
            inputs ^ 2 := by gcongr
      _ = 18 * inputs ^ 6 + inputs ^ 4 + inputs ^ 2 := by ring
      _ <= 20 * inputs ^ 6 := by omega
  have sixthLeEighth : inputs ^ 6 <= inputs ^ 8 :=
    Nat.pow_le_pow_right inputsPositive (by omega)
  rw [layerOverheadEnvelope_eq]
  dsimp only
  change resources *
        (inputs * (2 * sources * resources * (prefixWidth + 1))) +
      2 *
        (sources *
            (sources * (4 * prefixWidth + 4 * resources + 2) + sources) +
          sources) <= _
  calc
    resources *
          (inputs * (2 * sources * resources * (prefixWidth + 1))) +
        2 *
          (sources *
              (sources * (4 * prefixWidth + 4 * resources + 2) + sources) +
            sources) <=
      (2 * inputs ^ 2) * (inputs * (12 * inputs ^ 5)) +
        2 * (20 * inputs ^ 6) := by gcongr
    _ = 24 * inputs ^ 8 + 40 * inputs ^ 6 := by ring
    _ <= 64 * inputs ^ 8 := by omega

end UhligTheorem
end MassProduction
end Algebraic
