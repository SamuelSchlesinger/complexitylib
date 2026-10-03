/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Frobenius.Defs
public import Mathlib.Algebra.Polynomial.Div
import Complexitylib.Encoding.BitPolynomial
import Complexitylib.Encoding.BitPolynomial.Remainder

/-!
# Correctness and fixed widths of guarded modular squaring

The nonzero-modulus branch composes the checked multiplication and remainder
semantics. Induction over the count list gives the exponent `2^count.length`,
while reduction after every step bounds all states independently of that
exponent. The zero branch has exact width zero.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem frobeniusStep_length (modulus state : List Bool) :
    (frobeniusStep modulus state).length = significantLength modulus - 1 := by
  unfold frobeniusStep
  split_ifs with zero
  · simp only [List.length_nil, zero, Nat.zero_sub]
  · rw [BitPolynomial.remainderBits_length, ite_eq_right zero]

theorem frobeniusBits_length (a modulus count : List Bool) :
    (frobeniusBits a modulus count).length = significantLength modulus - 1 := by
  cases count with
  | nil =>
      unfold frobeniusBits
      split_ifs with zero
      · simp only [List.length_nil, zero, Nat.zero_sub]
      · rw [BitPolynomial.remainderBits_length, ite_eq_right zero]
  | cons bit tail => exact frobeniusStep_length modulus _

theorem frobeniusBits_length_le (a modulus count : List Bool) :
    (frobeniusBits a modulus count).length ≤ modulus.length := by
  rw [frobeniusBits_length]
  exact (Nat.sub_le _ _).trans (BitPolynomial.significantLength_le modulus)

theorem frobeniusBits_of_modulus_zero (a modulus count : List Bool)
    (zero : ofBits modulus = 0) : frobeniusBits a modulus count = [] := by
  have width := (BitPolynomial.significantLength_eq_zero_iff modulus).mpr zero
  cases count <;> simp only [frobeniusBits, frobeniusStep, width, ite_true]

theorem ofBits_frobeniusStep (modulus state : List Bool) (nonzero : ofBits modulus ≠ 0) :
    ofBits (frobeniusStep modulus state) = ofBits state ^ 2 %ₘ ofBits modulus := by
  have width := (BitPolynomial.significantLength_eq_zero_iff modulus).not.mpr nonzero
  rw [frobeniusStep, ite_eq_right width, BitPolynomial.ofBits_remainderBits,
    BitPolynomial.ofBits_mulBits, pow_two]

theorem ofBits_frobeniusBits (a modulus count : List Bool) (nonzero : ofBits modulus ≠ 0) :
    ofBits (frobeniusBits a modulus count) = ofBits a ^ (2 ^ count.length) %ₘ ofBits modulus := by
  have width := (BitPolynomial.significantLength_eq_zero_iff modulus).not.mpr nonzero
  induction count with
  | nil =>
      simp only [frobeniusBits, ite_eq_right width, List.length_nil, pow_zero, pow_one,
        BitPolynomial.ofBits_remainderBits]
  | cons bit tail ih =>
      rw [frobeniusBits, ofBits_frobeniusStep modulus _ nonzero, ih, List.length_cons,
        show 2 ^ (tail.length + 1) = 2 ^ tail.length * 2 from pow_succ 2 tail.length,
        pow_mul]
      simpa only [pow_two] using
        (Polynomial.mul_modByMonic (ofBits a ^ (2 ^ tail.length))
          (ofBits a ^ (2 ^ tail.length)) (ofBits modulus)).symm

theorem frobeniusEval_pair (a modulus count : List Bool) :
    frobeniusEval (pair (pair a modulus) count) = frobeniusBits a modulus count := by
  simp only [frobeniusEval, pairFst_pair, pairSnd_pair]

theorem frobeniusEval_length_le (z : List Bool) : (frobeniusEval z).length ≤ z.length :=
  (frobeniusBits_length_le _ _ _).trans
    ((pairSnd_length_le (pairFst z)).trans (pairFst_length_le z))

end BitPolynomial.Internal
end Complexity
