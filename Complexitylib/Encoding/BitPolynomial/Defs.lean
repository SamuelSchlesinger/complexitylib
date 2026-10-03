/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.Pairing
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Data.ZMod.Basic

/-!
# Binary coefficient lists and carryless multiplication

A list of bits represents a polynomial over `ZMod 2`, with its constant
coefficient first. Trailing false bits are high zero coefficients and may be
retained. `mulBits` computes every output coefficient as the parity of the
number of contributing pairs of true input coefficients.

The output has length `a.length + b.length`, including when one operand is
empty. For two nonempty inputs this leaves one high zero beyond the largest
possible nonzero product coefficient. This fixed length avoids trimming and
is convenient for subsequent bounded polynomial arithmetic.

This coefficient representation differs from the fixed natural-polynomial
Horner programs in `TM.binaryPolynomialEvalTM`: here both binary polynomials
are runtime inputs, and addition of coefficients is modulo two.
-/

@[expose] public section

namespace Complexity
namespace BitPolynomial

/-- Interpret a coefficient list over `ZMod 2`, with the constant coefficient first. -/
def ofBits (bits : List Bool) : Polynomial (ZMod 2) :=
  Polynomial.ofFn bits.length fun i => (bits[i].toNat : ZMod 2)

/-- Carryless multiplication, padded to the sum of the input lengths. -/
def mulBits (a b : List Bool) : List Bool :=
  (List.range (a.length + b.length)).map fun k =>
    decide (((Finset.range a.length).filter fun i =>
      i ≤ k ∧ a[i]?.getD false = true ∧ b[k - i]?.getD false = true).card % 2 = 1)

/-- Multiply two coefficient lists supplied through the standard pairing codec. -/
def mulEval (z : List Bool) : List Bool :=
  mulBits (pairFst z) (pairSnd z)

end BitPolynomial
end Complexity
