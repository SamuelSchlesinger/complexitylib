/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Defs
public import Mathlib.Data.Nat.Log

/-!
# Runtime coefficient lists for sparse binary trinomials

The list `trinomialBits d` has true coefficients at positions `0`, `d`, and
`2*d`, representing `X^(2*d) + X^d + 1` over the two-element field. The
definition is total at `d = 0`: all three positions coincide, and their sum
is still one in characteristic two. The evaluator takes `d` in unary as the
length of its input; the input bit values are ignored.
-/

@[expose] public section

namespace Complexity
namespace BitPolynomial

/-- The coefficient list of `X^(2*d) + X^d + 1`, including the case `d = 0`. -/
def trinomialBits (d : Nat) : List Bool :=
  (List.range (2 * d + 1)).map fun i => decide (i = 0 ∨ i = d ∨ i = 2 * d)

/-- Generate a sparse binary trinomial from a runtime unary half-degree. -/
def trinomialEval (z : List Bool) : List Bool := trinomialBits z.length

/-- Round a runtime unary target up to a power of three and generate its trinomial. -/
def roundedTrinomialEval (z : List Bool) : List Bool :=
  trinomialBits (3 ^ Nat.clog 3 z.length)

end BitPolynomial
end Complexity
