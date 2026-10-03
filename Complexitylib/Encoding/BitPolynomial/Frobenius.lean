/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Frobenius.Defs
public import Mathlib.Algebra.Polynomial.Div
import Complexitylib.Encoding.BitPolynomial.Frobenius.Internal

/-!
# Correct bounded binary modular Frobenius

For every nonzero runtime modulus, `frobeniusBits a modulus count` represents
`ofBits a ^ (2 ^ count.length) %ₘ ofBits modulus`. Its state always has exactly
`significantLength modulus - 1` bits, independently of the exponent. This
includes high zero padding, empty dividends, and constant-one moduli.

For a zero modulus the result is explicitly empty. The nested pairing
`pair (pair a modulus) count` supplies all three runtime inputs. Malformed
inputs follow the total pairing projections and the same guarded algorithm.
The uniform FP certificate is in `Complexitylib.Classes.P.BitPolynomial.Frobenius`.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Every guarded square-and-remainder step has the modulus's fixed degree width. -/
theorem frobeniusStep_length (modulus state : List Bool) :
    (frobeniusStep modulus state).length = significantLength modulus - 1 :=
  Internal.frobeniusStep_length modulus state

/-- Every state of the count-list fold has the modulus's fixed degree width. -/
theorem frobeniusBits_length (a modulus count : List Bool) :
    (frobeniusBits a modulus count).length = significantLength modulus - 1 :=
  Internal.frobeniusBits_length a modulus count

/-- Output length is bounded by the supplied modulus length for all inputs. -/
theorem frobeniusBits_length_le (a modulus count : List Bool) :
    (frobeniusBits a modulus count).length ≤ modulus.length :=
  Internal.frobeniusBits_length_le a modulus count

/-- A zero modulus produces the empty list, independently of the dividend or count. -/
theorem frobeniusBits_of_modulus_zero (a modulus count : List Bool)
    (zero : ofBits modulus = 0) : frobeniusBits a modulus count = [] :=
  Internal.frobeniusBits_of_modulus_zero a modulus count zero

/-- A guarded step computes one modular square whenever the modulus is nonzero. -/
theorem ofBits_frobeniusStep (modulus state : List Bool) (nonzero : ofBits modulus ≠ 0) :
    ofBits (frobeniusStep modulus state) = ofBits state ^ 2 %ₘ ofBits modulus :=
  Internal.ofBits_frobeniusStep modulus state nonzero

/-- The fold computes the requested modular power for every nonzero binary modulus. -/
theorem ofBits_frobeniusBits (a modulus count : List Bool) (nonzero : ofBits modulus ≠ 0) :
    ofBits (frobeniusBits a modulus count) = ofBits a ^ (2 ^ count.length) %ₘ ofBits modulus :=
  Internal.ofBits_frobeniusBits a modulus count nonzero

/-- Decoding the nested pairing recovers the exact dividend, modulus, and count list. -/
theorem frobeniusEval_pair (a modulus count : List Bool) :
    frobeniusEval (pair (pair a modulus) count) = frobeniusBits a modulus count :=
  Internal.frobeniusEval_pair a modulus count

/-- Even malformed paired inputs produce at most their input length in bits. -/
theorem frobeniusEval_length_le (z : List Bool) : (frobeniusEval z).length ≤ z.length :=
  Internal.frobeniusEval_length_le z

end BitPolynomial
end Complexity
