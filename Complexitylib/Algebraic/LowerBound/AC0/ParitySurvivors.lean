/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.ParityParameters

/-!
# Integer survivor schedules for parity depth reduction

The probabilistic schedule retains a real fraction of the live variables, but
the layer theorem requires natural-number targets. This module uses ordinary
floor division: divide once by `20`, then by `20t` at every later round.

The schedule is antitone, lies below the corresponding real retained ratio at
each step, and has the exact closed form

`a_(i+1) = n / (20 * (20*t)^i)`.

These are symbolic rounding lemmas. No parameter enumeration or numerical
experiment is involved.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace ParityParameters

open scoped ENNReal

/-- First-round and later-round integer divisors. -/
def retentionDivisor (t : Nat) : Nat → Nat
  | 0 => 20
  | _ + 1 => 20 * t

/-- Integer survivor targets obtained by iterated floor division. -/
def retained (n t : Nat) : Nat → Nat
  | 0 => n
  | level + 1 => retained n t level / retentionDivisor t level

@[simp] theorem retained_zero (n t : Nat) :
    retained n t 0 = n := rfl

@[simp] theorem retained_succ (n t level : Nat) :
    retained n t (level + 1) =
      retained n t level / retentionDivisor t level := by
  simp [retained]

/-- Each floor-division step can only decrease the target. -/
theorem retained_succ_le (n t level : Nat) :
    retained n t (level + 1) ≤ retained n t level := by
  rw [retained_succ]
  exact Nat.div_le_self _ _

/-- The integer survivor schedule is antitone in the round number. -/
theorem retained_antitone (n t : Nat) :
    Antitone (retained n t) :=
  antitone_nat_of_succ_le (retained_succ_le n t)

/-- Positivity of a later survivor target implies positivity at every earlier
round. -/
theorem retained_positive_of_final
    (n t : Nat)
    {level rounds : Nat}
    (levelLe : level ≤ rounds)
    (finalPositive : 0 < retained n t rounds) :
    0 < retained n t level :=
  finalPositive.trans_le (retained_antitone n t levelLe)

/-- Exact closed form for every positive-index survivor target. -/
theorem retained_closed
    (n t level : Nat) :
    retained n t (level + 1) =
      n / (20 * (20 * t) ^ level) := by
  induction level with
  | zero => simp [retained, retentionDivisor]
  | succ prior inductionHypothesis =>
      rw [retained_succ, inductionHypothesis,
        retentionDivisor, Nat.div_div_eq_div_mul, pow_succ]
      congr 1
      ac_rfl

/-- Floor division stays below the intended retained ratio, first stated in
the finite nonnegative reals. -/
theorem retained_shrinks_nnreal
    (n t level : Nat) :
    (retained n t (level + 1) : NNReal) ≤
      retentionRatio t level * (retained n t level : NNReal) := by
  rw [retained_succ]
  cases level with
  | zero =>
      simpa [retentionDivisor, retentionRatio, div_eq_mul_inv,
        mul_comm] using
        (Nat.cast_div_le (m := n) (n := 20) :
          ((n / 20 : Nat) : NNReal) ≤ (n : NNReal) / (20 : NNReal))
  | succ prior =>
      simpa [retentionDivisor, retentionRatio, div_eq_mul_inv,
        mul_comm] using
        (Nat.cast_div_le
          (m := retained n t (prior + 1)) (n := 20 * t) :
          (((retained n t (prior + 1)) / (20 * t) : Nat) : NNReal) ≤
            (retained n t (prior + 1) : NNReal) /
              ((20 * t : Nat) : NNReal))

/-- The floor-division inequality in the extended nonnegative reals used by
the probability schedule. -/
theorem retained_shrinks
    (n t level : Nat) :
    (retained n t (level + 1) : ENNReal) ≤
      (retentionRatio t level : ENNReal) *
        (retained n t level : ENNReal) := by
  change ((retained n t (level + 1) : NNReal) : ENNReal) ≤
    ((retentionRatio t level *
      (retained n t level : NNReal) : NNReal) : ENNReal)
  exact ENNReal.coe_le_coe.mpr (retained_shrinks_nnreal n t level)

end ParityParameters
end AC0
end Algebraic
