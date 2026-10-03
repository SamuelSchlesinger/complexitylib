/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Defs

/-!
# Padded addition of binary coefficient lists

Addition XORs coefficients at equal indices, reading false beyond either
operand. The output length is the larger input length, so missing high
coefficients are padded with zeros. Both operands are runtime inputs.
-/

@[expose] public section

namespace Complexity
namespace BitPolynomial

/-- Coefficientwise XOR, padding the shorter operand with high zero coefficients. -/
def addBits (a b : List Bool) : List Bool :=
  (List.range (max a.length b.length)).map fun i =>
    Bool.xor (a[i]?.getD false) (b[i]?.getD false)

/-- Add two coefficient lists supplied through the standard pairing codec. -/
def addEval (z : List Bool) : List Bool := addBits (pairFst z) (pairSnd z)

end BitPolynomial
end Complexity
