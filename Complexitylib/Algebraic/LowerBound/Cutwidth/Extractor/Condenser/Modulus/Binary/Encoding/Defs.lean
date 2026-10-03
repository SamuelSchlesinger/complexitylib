/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Frobenius.Defs
public import Complexitylib.Encoding.BitPolynomial.Trinomial.Defs

/-!
# Modular powering with a generated binary modulus

The evaluator reads a dividend, a requested half-degree, and a squaring count
through `pair (pair dividend target) count`. Both numerical parameters are
unary word lengths. It rounds the half-degree up to a power of three,
generates the corresponding trinomial, and performs bounded modular squaring.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Generate a binary modulus and square once per runtime count bit. -/
def encodedBinaryFrobenius (z : List Bool) : List Bool :=
  Complexity.BitPolynomial.frobeniusEval
    (Complexity.pair
      (Complexity.pair (Complexity.pairFst (Complexity.pairFst z))
        (Complexity.BitPolynomial.roundedTrinomialEval
          (Complexity.pairSnd (Complexity.pairFst z))))
      (Complexity.pairSnd z))

end Algebraic.Cutwidth.Extractor
