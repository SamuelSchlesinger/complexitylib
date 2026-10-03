/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Remainder.Defs

/-!
# Bounded modular Frobenius on binary coefficient lists

A count list requests one square-and-remainder step per bit, independently
of the bit values. The initial dividend is reduced before the first step.
Every state has the fixed width of the modulus degree.

A zero modulus produces the empty list at initialization and at every step.
This explicit convention keeps the total algorithm bounded: unreduced
successive squares could have exponential output length. Nonzero moduli may
have arbitrary high zero padding, and a constant-one modulus also gives the
empty list. The evaluator uses the codec `pair (pair a modulus) count`.
-/

@[expose] public section

namespace Complexity
namespace BitPolynomial

/-- Square and reduce a state, returning the empty list for a zero modulus. -/
def frobeniusStep (modulus state : List Bool) : List Bool :=
  if significantLength modulus = 0 then [] else
    remainderBits (mulBits state state) modulus

/-- Reduce a dividend, then square and reduce once per bit of the count list. -/
def frobeniusBits (a modulus : List Bool) : List Bool → List Bool
  | [] => if significantLength modulus = 0 then [] else remainderBits a modulus
  | _ :: tail => frobeniusStep modulus (frobeniusBits a modulus tail)

/-- The total evaluator on `pair (pair dividend modulus) count`. -/
def frobeniusEval (z : List Bool) : List Bool :=
  frobeniusBits (pairFst (pairFst z)) (pairSnd (pairFst z)) (pairSnd z)

end BitPolynomial
end Complexity
