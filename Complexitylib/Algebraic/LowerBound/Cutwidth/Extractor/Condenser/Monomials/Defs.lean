/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The first monomials in the GUV interpolation argument

The exponent vector of monomial `j` consists of its first `m` base-`h`
digits. The range `j < K ≤ h^m` indexes precisely the first `K` monomials,
allowing the interpolation argument to retain the actual source-set size.
Products suffice to evaluate these monomials without a separate multivariate
polynomial representation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Digit `i` of `j` in base `h`, beginning with the units digit. -/
def monomialDigit (h j : Nat) {m : Nat} (i : Fin m) : Nat :=
  j / h ^ i.val % h

/-- Evaluate the monomial whose exponents are the first base-`h` digits of `j`. -/
def digitMonomial {R : Type*} [CommMonoid R] {m : Nat}
    (h j : Nat) (z : Fin m → R) : R :=
  ∏ i, z i ^ monomialDigit h j i

end Algebraic.Cutwidth.Extractor
