/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Long division of binary coefficient lists

`significantLength` discards high zero padding numerically: it is one past the
highest true coefficient, or zero for the zero polynomial. Every nonzero
binary polynomial is monic, independently of its list's high zero padding.

For a modulus of degree `d`, `remainderScan` processes the dividend from its
highest coefficient to its constant coefficient, keeping exactly `d` bits.
Each step shifts the current remainder, inserts the next coefficient, and
cancels the possible degree-`d` term with the supplied modulus. Constant-one
moduli have `d = 0` and produce the empty list.

`remainderBits` returns its dividend unchanged for a zero modulus, agreeing
with Mathlib's convention for remainder by a nonmonic zero polynomial. Both
operands are runtime inputs, and every definition is total.
-/

@[expose] public section

namespace Complexity
namespace BitPolynomial

/-- One past the highest true coefficient, or zero for an all-false list. -/
def significantLength (bits : List Bool) : Nat :=
  (Finset.range bits.length).sup fun i => if bits[i]?.getD false then i + 1 else 0

/-- One long-division step, retaining exactly the modulus degree in coefficients. -/
def remainderStep (modulus : List Bool) (bit : Bool) (state : List Bool) : List Bool :=
  let d := significantLength modulus - 1
  let shifted := bit :: state
  (List.range d).map fun i =>
    Bool.xor (shifted[i]?.getD false)
      (shifted[d]?.getD false && modulus[i]?.getD false)

/-- Scan a little-endian dividend from its high coefficients to its low coefficients. -/
def remainderScan (modulus : List Bool) : List Bool → List Bool
  | [] => List.replicate (significantLength modulus - 1) false
  | bit :: tail => remainderStep modulus bit (remainderScan modulus tail)

/-- Remainder by a runtime binary modulus, allowing high zeros and the zero polynomial. -/
def remainderBits (a modulus : List Bool) : List Bool :=
  if significantLength modulus = 0 then a else remainderScan modulus a

/-- The total paired-input evaluator for binary-polynomial remainder. -/
def remainderEval (z : List Bool) : List Bool :=
  remainderBits (pairFst z) (pairSnd z)

end BitPolynomial
end Complexity
