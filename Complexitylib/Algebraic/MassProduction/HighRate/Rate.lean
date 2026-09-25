/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.DigitMonomials
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# Rate one with an explicit finite cutoff

The retained dimension is `A^m - (A-1)^m`. Bernoulli's inequality gives the
integer precision statement `precision * A^m <= (precision+1) * dimension`
as soon as `m >= precision * (A-1)` and `m > 0`. No real asymptotic
notation or unproved limiting step is needed.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

/-- Exact size of the family containing an all-zero digit column. -/
def retainedDimension (alphabet blocks : Nat) : Nat :=
  alphabet ^ blocks - (alphabet - 1) ^ blocks

/-- A finite rate guarantee, with an explicit cutoff linear in precision. -/
theorem retainedDimension_rate
    (alphabet blocks precision : Nat)
    (alphabetPositive : 0 < alphabet) (blocksPositive : 0 < blocks)
    (blocksLarge : precision * (alphabet - 1) ≤ blocks) :
    precision * alphabet ^ blocks ≤ (precision + 1) * retainedDimension alphabet blocks := by
  have predecessor : alphabet - 1 + 1 = alphabet := Nat.sub_add_cancel alphabetPositive
  have bernoulli := pow_add_mul_le_add_pow (a := alphabet - 1) (b := 1)
    (Nat.zero_le _) (Nat.zero_le _) blocks
  simp only [predecessor, mul_one, Nat.cast_id] at bernoulli
  have oneZeroLe : blocks * (alphabet - 1) ^ (blocks - 1) ≤
      retainedDimension alphabet blocks := by
    apply Nat.le_sub_of_add_le
    exact (Nat.add_comm _ _).trans_le bernoulli
  have precisionMissing : precision * (alphabet - 1) ^ blocks ≤
      retainedDimension alphabet blocks := by
    calc
      _ = (precision * (alphabet - 1)) * (alphabet - 1) ^ (blocks - 1) := by
        conv_lhs => arg 2; rw [← Nat.sub_add_cancel blocksPositive, pow_succ']
        ring
      _ ≤ blocks * (alphabet - 1) ^ (blocks - 1) := Nat.mul_le_mul_right _ blocksLarge
      _ ≤ _ := oneZeroLe
  have missingLe : (alphabet - 1) ^ blocks ≤ alphabet ^ blocks :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have partition : retainedDimension alphabet blocks + (alphabet - 1) ^ blocks =
      alphabet ^ blocks := Nat.sub_add_cancel missingLe
  calc
    _ = precision * retainedDimension alphabet blocks + precision * (alphabet - 1) ^ blocks := by
      rw [← partition]
      ring
    _ ≤ precision * retainedDimension alphabet blocks + retainedDimension alphabet blocks :=
      Nat.add_le_add_left precisionMissing _
    _ = _ := by ring

/-- The dimension approaches the full table size in the integer precision
form used by the circuit-cost statements. -/
theorem retainedDimension_hasRateOne (alphabet : Nat) (alphabetPositive : 0 < alphabet) :
    ∀ precision, ∃ cutoff, ∀ blocks, cutoff ≤ blocks →
      precision * alphabet ^ blocks ≤ (precision + 1) * retainedDimension alphabet blocks := by
  intro precision
  refine ⟨max 1 (precision * (alphabet - 1)), ?_⟩
  intro blocks large
  apply retainedDimension_rate alphabet blocks precision alphabetPositive
  · have := (le_max_left 1 (precision * (alphabet - 1))).trans large
    omega
  · exact (le_max_right 1 (precision * (alphabet - 1))).trans large

end Algebraic.MassProduction.HighRate
