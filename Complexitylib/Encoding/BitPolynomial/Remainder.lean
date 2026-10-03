/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Remainder.Defs
public import Mathlib.Algebra.Polynomial.Div
import Complexitylib.Encoding.BitPolynomial.Remainder.Internal
import Complexitylib.Encoding.BitPolynomial.Remainder.Internal.Step
import Complexitylib.Encoding.BitPolynomial.Remainder.Internal.Width

/-!
# Correct binary-polynomial remainder with a runtime modulus

`ofBits_remainderBits` identifies the concrete list algorithm with polynomial
remainder over `ZMod 2` for every dividend and modulus. High zero padding does
not change the modulus. A zero modulus returns the original dividend, while
a constant-one modulus produces the empty coefficient list.

The high-to-low scan stores exactly the modulus degree in bits. Its width is
bounded by the supplied modulus length, and the total evaluator's output is
bounded by the larger input length. The uniform polynomial-time certificate
is in `Complexitylib.Classes.P.BitPolynomial.Remainder`.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- The significant coefficient width never exceeds the input length. -/
theorem significantLength_le (bits : List Bool) : significantLength bits ≤ bits.length :=
  Internal.significantLength_le bits

/-- Significant width zero means exactly that all represented coefficients are zero. -/
theorem significantLength_eq_zero_iff (bits : List Bool) :
    significantLength bits = 0 ↔ ofBits bits = 0 :=
  Internal.significantLength_eq_zero_iff bits

/-- For a nonzero polynomial, significant width is one past its degree. -/
theorem ofBits_natDegree (bits : List Bool) (nonzero : ofBits bits ≠ 0) :
    (ofBits bits).natDegree = significantLength bits - 1 :=
  (Internal.ofBits_isMonicOfDegree bits (Nat.pos_of_ne_zero fun h =>
    nonzero ((significantLength_eq_zero_iff bits).mp h))).natDegree_eq

/-- Every cancellation step restores the fixed width, including width zero. -/
theorem remainderStep_length (modulus : List Bool) (bit : Bool) (state : List Bool) :
    (remainderStep modulus bit state).length = significantLength modulus - 1 :=
  Internal.remainderStep_length modulus bit state

/-- Every intermediate scan state has the fixed remainder width. -/
theorem remainderScan_length (modulus a : List Bool) :
    (remainderScan modulus a).length = significantLength modulus - 1 :=
  Internal.remainderScan_length modulus a

/-- Exact output length, with the unchanged-dividend convention for a zero modulus. -/
theorem remainderBits_length (a modulus : List Bool) :
    (remainderBits a modulus).length =
      if significantLength modulus = 0 then a.length else significantLength modulus - 1 :=
  Internal.remainderBits_length a modulus

/-- The output length is bounded by the larger operand length. -/
theorem remainderBits_length_le (a modulus : List Bool) :
    (remainderBits a modulus).length ≤ max a.length modulus.length :=
  Internal.remainderBits_length_le a modulus

/-- The total bit-list algorithm computes polynomial remainder for every modulus. -/
theorem ofBits_remainderBits (a modulus : List Bool) :
    ofBits (remainderBits a modulus) = ofBits a %ₘ ofBits modulus :=
  Internal.ofBits_remainderBits a modulus

/-- The evaluator reads its dividend and modulus from the standard pairing codec. -/
theorem remainderEval_pair (a modulus : List Bool) :
    remainderEval (pair a modulus) = remainderBits a modulus := by
  simp only [remainderEval, pairFst_pair, pairSnd_pair]

end BitPolynomial
end Complexity
