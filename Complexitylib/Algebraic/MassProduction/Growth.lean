/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.CircuitFamily.Growth
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring

/-!
# Elementary eventual growth bounds for mass production

The manuscript repeatedly uses that a fixed positive linear gap between
binary exponents absorbs every fixed polynomial factor.  This file packages
that step in exact natural-number form, with eventual quantifiers only at the
outer boundary.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Growth

open Filter

/-- The sum of two floored quotients is at most the floor of the sum. -/
theorem div_add_div_le
    (left right divisor : Nat)
    (divisorPositive : 0 < divisor) :
    left / divisor + right / divisor <= (left + right) / divisor := by
  rw [Nat.add_div divisorPositive]
  omega

/-- Every fixed natural polynomial monomial, including a fixed coefficient,
is eventually bounded by the matching binary exponential. -/
theorem eventually_const_mul_pow_le_two_pow
    (constant degree : Nat) :
    ∀ᶠ n in atTop, constant * n ^ degree <= 2 ^ n :=
  Circuit.Resource.eventually_const_mul_pow_le_two_pow constant degree

/-- A fixed polynomial is also absorbed by the exponential carried by any
fixed positive fraction `n / divisor` of the input length. -/
theorem eventually_const_mul_pow_le_two_pow_div
    (constant degree divisor : Nat)
    (divisorPositive : 0 < divisor) :
    ∀ᶠ n in atTop,
      constant * n ^ degree <= 2 ^ (n / divisor) := by
  let enlarged := constant * divisor ^ degree * 2 ^ degree
  obtain ⟨cutoff, pastCutoff⟩ := eventually_atTop.1
    (eventually_const_mul_pow_le_two_pow enlarged degree)
  apply eventually_atTop.2
  refine ⟨divisor * max cutoff 1, fun n nLarge => ?_⟩
  let quotient := n / divisor
  have quotientLarge : max cutoff 1 <= quotient := by
    apply (Nat.le_div_iff_mul_le divisorPositive).2
    simpa only [Nat.mul_comm] using nLarge
  have quotientPositive : 1 <= quotient :=
    (le_max_right cutoff 1).trans quotientLarge
  have inputBound : n <= divisor * (quotient + 1) := by
    exact Nat.le_of_lt (Nat.lt_mul_div_succ n divisorPositive)
  have successorBound : quotient + 1 <= 2 * quotient := by omega
  calc
    constant * n ^ degree <=
        constant * (divisor * (quotient + 1)) ^ degree := by
      gcongr
    _ <= constant * (divisor * (2 * quotient)) ^ degree := by
      gcongr
    _ = enlarged * quotient ^ degree := by
      simp only [enlarged, mul_pow]
      ring
    _ <= 2 ^ quotient := pastCutoff quotient
      ((le_max_left cutoff 1).trans quotientLarge)

/-- A strict gap between two rational binary exponents absorbs a fixed
polynomial coefficient.  Natural division implements both floors. -/
theorem eventually_mul_two_pow_rational_le
    (constant degree low high denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (gap : low < high) :
    ∀ᶠ n in atTop,
      constant * n ^ degree * 2 ^ (low * n / denominator) <=
        2 ^ (high * n / denominator) := by
  filter_upwards [eventually_const_mul_pow_le_two_pow_div
      constant degree denominator denominatorPositive] with n polynomialBound
  have exponentBound :
      low * n / denominator + n / denominator <=
        high * n / denominator := by
    have nextLe : low + 1 <= high := by omega
    calc
      low * n / denominator + n / denominator <=
          (low * n + n) / denominator := by
        rw [Nat.add_div denominatorPositive]
        omega
      _ = (low + 1) * n / denominator := by
        rw [Nat.add_mul, one_mul]
      _ <= high * n / denominator :=
        Nat.div_le_div_right (Nat.mul_le_mul_right n nextLe)
  calc
    constant * n ^ degree * 2 ^ (low * n / denominator) <=
        2 ^ (n / denominator) *
          2 ^ (low * n / denominator) := by
      gcongr
    _ = 2 ^ (low * n / denominator + n / denominator) := by
      rw [Nat.pow_add]
      ring
    _ <= 2 ^ (high * n / denominator) :=
      Nat.pow_le_pow_right (by omega) exponentBound

/-- If a rational exponent is strictly below one, the same exponential
margin absorbs both a fixed polynomial and the denominator `n` in the sharp
Shannon scale `2^n / n`. -/
theorem eventually_mul_two_pow_rational_le_shannonScale
    (constant degree numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (proper : numerator < denominator) :
    ∀ᶠ n in atTop,
      constant * n ^ degree * 2 ^ (numerator * n / denominator) <=
        2 ^ n / n := by
  have absorbed := eventually_mul_two_pow_rational_le
    constant (degree + 1) numerator denominator denominator
    denominatorPositive proper
  filter_upwards [absorbed, eventually_ge_atTop 1] with n bound nPositive
  rw [Nat.le_div_iff_mul_le nPositive]
  calc
    constant * n ^ degree * 2 ^ (numerator * n / denominator) * n =
        constant * n ^ (degree + 1) *
          2 ^ (numerator * n / denominator) := by
      rw [pow_succ]
      ring
    _ <= 2 ^ (denominator * n / denominator) := bound
    _ = 2 ^ n := by rw [Nat.mul_div_cancel_left n denominatorPositive]

/-- Doubling a positive denominator changes a sufficiently nonzero natural
quotient by at most a factor four.  This coarse floor-stable form is useful
when comparing equal-block resource terms with `2^n / n`. -/
theorem div_le_four_mul_double_div
    (value divisor : Nat)
    (divisorPositive : 0 < divisor)
    (twoDivisorFits : 2 * divisor <= value) :
    value / divisor <= 4 * (value / (2 * divisor)) := by
  let quotient := value / (2 * divisor)
  have doubledPositive : 0 < 2 * divisor := by omega
  have quotientPositive : 1 <= quotient := by
    apply (Nat.le_div_iff_mul_le doubledPositive).2
    simpa only [one_mul] using twoDivisorFits
  have valueBelow : value < 2 * divisor * (quotient + 1) := by
    exact Nat.lt_mul_div_succ value doubledPositive
  have dividedBound : value / divisor <=
      (2 * divisor * (quotient + 1)) / divisor :=
    Nat.div_le_div_right (Nat.le_of_lt valueBelow)
  calc
    value / divisor <= (2 * divisor * (quotient + 1)) / divisor :=
      dividedBound
    _ = 2 * (quotient + 1) := by
      rw [show 2 * divisor * (quotient + 1) =
        (2 * (quotient + 1)) * divisor by ring,
        Nat.mul_div_cancel _ divisorPositive]
    _ <= 4 * quotient := by omega

/-- Pulling a fixed coefficient outside natural division costs at most a
factor two once the quotient is nonzero. -/
theorem mul_div_le_two_mul_mul_div
    (constant value divisor : Nat)
    (divisorPositive : 0 < divisor)
    (divisorFits : divisor <= value) :
    constant * value / divisor <=
      2 * constant * (value / divisor) := by
  let quotient := value / divisor
  have quotientPositive : 1 <= quotient := by
    apply (Nat.le_div_iff_mul_le divisorPositive).2
    simpa only [one_mul] using divisorFits
  have valueBound : value <= divisor * (2 * quotient) := by
    exact (Nat.le_of_lt (Nat.lt_mul_div_succ value divisorPositive)).trans
      (Nat.mul_le_mul_left divisor (by omega))
  calc
    constant * value / divisor <=
        (constant * (divisor * (2 * quotient))) / divisor :=
      Nat.div_le_div_right (Nat.mul_le_mul_left constant valueBound)
    _ = 2 * constant * quotient := by
      rw [show constant * (divisor * (2 * quotient)) =
        (2 * constant * quotient) * divisor by ring,
        Nat.mul_div_cancel _ divisorPositive]

end Growth
end MassProduction
end Algebraic
