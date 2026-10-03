/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Interpolation.Internal

/-!
# The finite interpolation step for condenser expansion

For any fixed feature values, fewer than `A * K` evaluation constraints admit
a nonzero family of `K` coefficient polynomials, each of degree less than `A`.
In the Guruswami--Umans--Vadhan expansion proof (2009), Section 3.1, the features
are the first `K` base-`h` monomials evaluated at a neighbor tuple. The parameter
`K` is the actual source size, not the maximum `h^m` allowed by the construction.

This theorem proves existence of the interpolating witness by linear algebra.
It is part of the expansion proof, not an algorithm used to evaluate the
condenser. Removing common modulus factors and proving the root-count bound
are separate steps.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Fewer scalar constraints than coefficients leave a nonzero interpolant.
The constraint type is arbitrary; source seeds and feature weights are fixed
before the coefficient family is chosen. -/
theorem exists_polynomial_interpolant {F X : Type*} [Field F] {A K : Nat}
    (T : Finset X) (seed : X → F) (weight : X → Fin K → F)
    (budget : T.card < A * K) :
    ∃ p : Fin K → Polynomial F, p ≠ 0 ∧
      (∀ j, (p j).degree < A) ∧
      ∀ x ∈ T, ∑ j, (p j).eval (seed x) * weight x j = 0 :=
  Internal.exists_polynomial_interpolant T seed weight budget

end Algebraic.Cutwidth.Extractor
