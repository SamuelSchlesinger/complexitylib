/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Basic

/-!
# A sparse binary modulus family

The trinomial `X^(2 * 3^s) + X^(3^s) + 1` has a fixed description for every
exponent. These are semantic polynomials over `ZMod 2`; their encoded
coefficient vectors and runtime construction are separate definitions.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The binary trinomial used for a field of cardinality `2^(2 * 3^s)`. -/
noncomputable def binaryModulus (s : Nat) : Polynomial (ZMod 2) :=
  Polynomial.X ^ (2 * 3 ^ s) + Polynomial.X ^ (3 ^ s) + 1

end Algebraic.Cutwidth.Extractor
