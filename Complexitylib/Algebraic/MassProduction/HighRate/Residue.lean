/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# The residue obstruction behind the high-rate code

A positive exponent below `dimension * (q - 1)` cannot be divisible by
`q - 1` if its residue modulo a divisor of `q` is at most
`modulus - dimension`. A common block of zero binary digits supplies exactly
this residue gap.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators

/-- A small residue excludes every positive multiple of `q - 1` below
`dimension * (q - 1)`. -/
theorem notDvdOfResidueGap
    (q dimension modulus exponent : Nat)
    (modulusDivides : modulus ∣ q)
    (exponentPositive : 0 < exponent)
    (exponentSmall : exponent < dimension * (q - 1))
    (residueGap : exponent % modulus + dimension ≤ modulus) :
    ¬ (q - 1) ∣ exponent := by
  rintro ⟨multiple, exponentEquation⟩
  have qLarge : 1 < q := by
    by_contra h
    have : q - 1 = 0 := by omega
    simp [this] at exponentSmall
  have multiplePositive : 0 < multiple := by
    by_contra h
    have : multiple = 0 := by omega
    simp [this] at exponentEquation
    omega
  have multipleSmall : multiple < dimension := by
    apply Nat.lt_of_mul_lt_mul_left (a := q - 1)
    calc
      (q - 1) * multiple = exponent := exponentEquation.symm
      _ < dimension * (q - 1) := exponentSmall
      _ = (q - 1) * dimension := Nat.mul_comm _ _
  have multipleSmallModulus : multiple < modulus := by omega
  have sumSmall : exponent % modulus + multiple < modulus := by omega
  have sumDivisible : modulus ∣ exponent + multiple := by
    have equation : exponent + multiple = q * multiple := by
      rw [exponentEquation]
      calc
        (q - 1) * multiple + multiple = (q - 1 + 1) * multiple := by ring
        _ = q * multiple := by rw [Nat.sub_add_cancel (by omega)]
    rw [equation]
    exact dvd_mul_of_dvd_left modulusDivides _
  have sumRemainder := Nat.mod_eq_zero_of_dvd sumDivisible
  rw [Nat.add_mod, Nat.mod_eq_of_lt multipleSmallModulus,
    Nat.mod_eq_of_lt sumSmall] at sumRemainder
  omega

/-- A common zero block starts at `start` and contains `blockWidth` binary
digits in every coordinate exponent. -/
def CommonZeroBlock {Coordinate : Type*}
    (degrees : Coordinate → Nat) (start blockWidth : Nat) : Prop :=
  ∀ coordinate, degrees coordinate % 2 ^ (start + blockWidth) < 2 ^ start

/-- The residue definition is equivalent to the usual quotient-and-mask
test that the indicated block of binary digits is zero. -/
theorem commonZeroBlock_iff
    {Coordinate : Type*} (degrees : Coordinate → Nat) (start blockWidth : Nat) :
    CommonZeroBlock degrees start blockWidth ↔
      ∀ coordinate, degrees coordinate / 2 ^ start % 2 ^ blockWidth = 0 := by
  unfold CommonZeroBlock
  apply forall_congr'
  intro coordinate
  rw [← Nat.mod_mul_right_div_self, ← pow_add]
  rw [Nat.div_eq_zero_iff]
  simp

/-- The predecessor of a positive multiple of a modulus has the last
possible residue. -/
theorem predResidueOfDvd (q modulus : Nat)
    (qPositive : 0 < q) (modulusPositive : 0 < modulus) (divides : modulus ∣ q) :
    (q - 1) % modulus = modulus - 1 := by
  have residueSmall := Nat.mod_lt (q - 1) modulusPositive
  have successorZero : ((q - 1) % modulus + 1) % modulus = 0 := by
    rw [Nat.mod_add_mod, Nat.sub_add_cancel qPositive, Nat.mod_eq_zero_of_dvd divides]
  have modulusLe : modulus ≤ (q - 1) % modulus + 1 := by
    by_contra! below
    rw [Nat.mod_eq_of_lt below] at successorZero
    omega
  omega

/-- A reduced exponent containing a nonempty zero block is strictly below
`q - 1`, when `q` is a power of two covering that block. -/
theorem exponentLtCardPredOfZeroBlock
    (width start blockWidth exponent : Nat)
    (blockPositive : 0 < blockWidth) (blockFits : start + blockWidth ≤ width)
    (reduced : exponent < 2 ^ width)
    (zeroBlock : exponent % 2 ^ (start + blockWidth) < 2 ^ start) :
    exponent < 2 ^ width - 1 := by
  have widthPositive : 0 < (2 : Nat) ^ width := by positivity
  have blockPowerPositive : 0 < (2 : Nat) ^ (start + blockWidth) := by positivity
  have powerDivides : (2 : Nat) ^ (start + blockWidth) ∣ 2 ^ width :=
    Nat.pow_dvd_pow 2 blockFits
  have lastResidue := predResidueOfDvd (2 ^ width) (2 ^ (start + blockWidth))
    widthPositive blockPowerPositive powerDivides
  have blockLarger : (2 : Nat) ^ start < 2 ^ (start + blockWidth) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  by_contra! tooLarge
  have equalLast : exponent = 2 ^ width - 1 := by omega
  rw [equalLast, lastResidue] at zeroBlock
  omega

/-- Summing the low residues of all coordinates leaves a gap of at least
the dimension, provided the block has enough distinct bit patterns. -/
theorem commonZeroBlockSumResidueGap
    {Coordinate : Type*} [Fintype Coordinate]
    (degrees : Coordinate → Nat) (start blockWidth : Nat)
    (zeroBlock : CommonZeroBlock degrees start blockWidth)
    (dimensionFits : Fintype.card Coordinate ≤ 2 ^ blockWidth) :
    (∑ coordinate, degrees coordinate % 2 ^ (start + blockWidth)) +
        Fintype.card Coordinate ≤ 2 ^ (start + blockWidth) := by
  have lowPositive : 0 < (2 : Nat) ^ start := by positivity
  calc
    _ ≤ (∑ _coordinate : Coordinate, (2 ^ start - 1)) + Fintype.card Coordinate := by
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro coordinate _
      exact Nat.le_sub_one_of_lt (zeroBlock coordinate)
    _ = Fintype.card Coordinate * 2 ^ start := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      calc
        _ = Fintype.card Coordinate * (2 ^ start - 1 + 1) := by ring
        _ = _ := by rw [Nat.sub_add_cancel (by omega)]
    _ ≤ 2 ^ blockWidth * 2 ^ start := Nat.mul_le_mul_right _ dimensionFits
    _ = _ := by rw [← pow_add, Nat.add_comm]

end Algebraic.MassProduction.HighRate
