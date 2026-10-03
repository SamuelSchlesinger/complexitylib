/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Reserves
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of the explicit advice parameters

The logarithms of the two enlarged widths are bounded through powers of two,
retaining the scale's ample fixed slack. The three entropy reserves follow
from the previously checked finite error budget. No source distribution or
capacity of the chosen reserve in the left input is asserted here.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem clog_two_succ_le (a : Nat) : Nat.clog 2 (a + 1) ≤ a :=
  Nat.clog_le_of_le_pow (show a < 2 ^ a from Nat.lt_two_pow_self)

private theorem clog_two_scaled_succ_le (r a b : Nat) :
    Nat.clog 2 (2 ^ r * (a + 1) * (1024 * b) + 1) ≤ r + a + b + 11 := by
  have ha : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have hb : b ≤ 2 ^ b := (Nat.lt_two_pow_self).le
  have bound : 2 ^ r * (a + 1) * (1024 * b) ≤ 2 ^ (r + a + b + 10) := by
    calc
      _ ≤ 2 ^ r * 2 ^ a * (1024 * 2 ^ b) := by gcongr
      _ = _ := by simp only [pow_add]; norm_num; ring
  apply Nat.clog_le_of_le_pow
  calc
    _ ≤ 2 ^ (r + a + b + 10) + 1 := Nat.add_le_add_right bound 1
    _ ≤ 2 ^ (r + a + b + 10) * 2 := by
      have positive : 0 < (2 : Nat) ^ (r + a + b + 10) := by positivity
      lia
    _ = _ := (pow_succ 2 (r + a + b + 10)).symm

theorem adviceParameters_error_le (n a target out : Nat) :
    adviceErrorExponent a target ≤ adviceScale n a target out := by
  have log := clog_two_succ_le a
  simp only [adviceErrorExponent, adviceScale]
  lia

theorem adviceParameters_sizeGuard (n a target out : Nat) :
    FlipFlopSizeGuard n (adviceSourceEntropy n a target out)
      (adviceScale n a target out) (adviceErrorExponent a target) := by
  have log := clog_two_succ_le a
  have source := clog_two_scaled_succ_le 150 a
    (a + target + out + Nat.clog 2 (n + 1) + 256)
  have state := clog_two_scaled_succ_le 64 0
    (a + target + out + Nat.clog 2 (n + 1) + 256)
  simp only [zero_add, mul_one] at state
  simp only [FlipFlopSizeGuard, adviceSourceEntropy, adviceScale, adviceErrorExponent,
    matchedBlockOutputBits]
  exact ⟨by lia, by lia, source.trans (by lia), state.trans (by lia)⟩

theorem adviceParameters_stateWidth_le (n a target out : Nat) :
    matchedBlockOutputBits 64 (adviceScale n a target out) ≤
      adviceSourceEntropy n a target out := by
  simp only [matchedBlockOutputBits, adviceSourceEntropy]
  apply Nat.mul_le_mul_right
  norm_num
  lia

theorem adviceParameters_output_le (n a target out : Nat) :
    out ≤ matchedBlockSeedBits (adviceScale n a target out) := by
  simp only [matchedBlockSeedBits, adviceScale]
  norm_num
  lia

theorem adviceParameters_state_reserve (n a target out : Nat) :
    2 ^ 62 * adviceScale n a target out +
        2 * matchedBlockSeedBits (adviceScale n a target out) +
        adviceErrorExponent a target ≤
      matchedBlockOutputBits 64 (adviceScale n a target out) :=
  advice_state_entropy_gap (adviceParameters_error_le n a target out)

theorem adviceParameters_left_reserve (n a target out : Nat) :
    2 ^ 62 * adviceScale n a target out +
        (8 * a + 7) * matchedBlockSeedBits (adviceScale n a target out) +
        adviceErrorExponent a target ≤ adviceSourceEntropy n a target out :=
  advice_left_entropy_reserve (adviceParameters_error_le n a target out)

theorem adviceParameters_right_reserve (n a target out : Nat) :
    2 ^ 142 * adviceScale n a target out +
        (5 * a + 5) * matchedBlockOutputBits 64 (adviceScale n a target out) +
        adviceErrorExponent a target ≤ adviceSourceEntropy n a target out :=
  advice_right_entropy_reserve (adviceParameters_error_le n a target out)

end Algebraic.Cutwidth.Extractor.Internal
