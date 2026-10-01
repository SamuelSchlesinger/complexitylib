/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-!
# Approximate-counting error budgets

Shared arithmetic for converting the number of bad hashing levels into a
power-of-two failure bound. This module is independent of the weak and relative
counter constructions; the weak counter uses the specialization to two failure bits.
-/

public section

namespace Complexity
namespace ApproximateCounting

private theorem add_four_le_two_pow_add_two (n : ℕ) :
    n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.pow_succ]
      have hp : 1 ≤ 2 ^ (n + 2) := Nat.one_le_two_pow
      omega

/-- Shared union-bound arithmetic for weak and relative approximate counters. -/
theorem add_four_div_two_pow_errorBits_le_internal
    (n failureBits : ℕ) :
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 2 + failureBits) ≤
      1 / (2 : ℚ) ^ failureBits := by
  calc
    (n + 4 : ℚ) / (2 : ℚ) ^ (n + 2 + failureBits) ≤
        (2 : ℚ) ^ (n + 2) / (2 : ℚ) ^ (n + 2 + failureBits) := by
      gcongr
      exact_mod_cast add_four_le_two_pow_add_two n
    _ = 1 / (2 : ℚ) ^ failureBits := by
      have hdenominator :
          (2 : ℚ) ^ (n + 2 + failureBits) =
            (2 : ℚ) ^ (n + 2) * (2 : ℚ) ^ failureBits := by
        rw [show n + 2 + failureBits = (n + 2) + failureBits by omega,
          pow_add]
      rw [hdenominator]
      field_simp

end ApproximateCounting
end Complexity
