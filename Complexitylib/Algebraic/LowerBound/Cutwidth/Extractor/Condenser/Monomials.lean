/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials.Defs
public import Mathlib.Algebra.Polynomial.OfFn
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials.Internal

/-!
# Exact substitution for the first GUV interpolation monomials

For every `j < K ≤ h^m`, the first `m` base-`h` digits reconstruct `j`.
Their sum is at most `m * (h - 1)`. Consequently substituting `Z^(h^i)` into
the associated monomial gives exactly `Z^j`.

For a coefficient array indexed by `Fin K`, the substituted polynomial has
degree less than `K` and is nonzero precisely when some coefficient is nonzero.
The coefficient ring can be a quotient by the extension modulus, so this is
the nonvanishing step used after reduction of the interpolation coefficients.
No field or characteristic assumption is required by this layer.

This is the base-`h` monomial indexing in Guruswami, Umans, and Vadhan,
*Unbalanced Expanders and Randomness Extractors from Parvaresh--Vardy Codes*
(2009), Section 3.1, proof of Theorem 3.3:
https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf.
The bounds retain the given `K`, including when `K < h^m`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Each digit is below a positive base. -/
theorem monomialDigit_lt {h j m : Nat} (positive : 0 < h) (i : Fin m) :
    monomialDigit h j i < h :=
  Internal.monomialDigit_lt positive i

/-- The first `m` digits reconstruct every integer below `h^m`. -/
theorem sum_monomialDigit_mul_pow {h j m : Nat} (bound : j < h ^ m) :
    (∑ i : Fin m, monomialDigit h j i * h ^ i.val) = j :=
  Internal.sum_monomialDigit_mul_pow bound

/-- The total exponent of every digit monomial is at most `m * (h - 1)`. -/
theorem sum_monomialDigit_le {h j m : Nat} (positive : 0 < h) :
    (∑ i : Fin m, monomialDigit h j i) ≤ m * (h - 1) :=
  Internal.sum_monomialDigit_le positive

/-- Substituting powers with weights `h^i` recovers exactly the power indexed
by the encoded integer. This holds in any commutative monoid. -/
theorem digitMonomial_pow {R : Type*} [CommMonoid R] {h j m : Nat}
    (bound : j < h ^ m) (u : R) :
    digitMonomial h j (fun i : Fin m => u ^ (h ^ i.val)) = u ^ j :=
  Internal.digitMonomial_pow bound u

/-- Substitution in the first `K` monomials preserves their distinct indices
as univariate powers, without replacing `K` by `h^m`. -/
theorem digitMonomial_substitution {R : Type*} [CommSemiring R] {h K m : Nat}
    (bound : K ≤ h ^ m) (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.C (a j) *
      digitMonomial h j.val (fun i : Fin m => Polynomial.X ^ (h ^ i.val))) =
        ∑ j : Fin K, Polynomial.monomial j.val (a j) :=
  Internal.digitMonomial_substitution bound a

/-- The resulting monomial sum is the polynomial with coefficient array `a`. -/
theorem fin_monomial_sum_eq_ofFn {R : Type*} [Semiring R] [DecidableEq R]
    {K : Nat} (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)) = Polynomial.ofFn K a :=
  Internal.fin_monomial_sum_eq_ofFn a

/-- Each coefficient survives at its own exponent index. -/
theorem fin_monomial_sum_coeff {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) (j : Fin K) :
    (∑ i : Fin K, Polynomial.monomial i.val (a i)).coeff j.val = a j :=
  Internal.fin_monomial_sum_coeff a j

/-- The first `K` powers give degree strictly below `K`, including `K = 0`. -/
theorem fin_monomial_sum_degree_lt {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)).degree < K :=
  Internal.fin_monomial_sum_degree_lt a

/-- A coefficient surviving reduction makes the substituted polynomial nonzero. -/
theorem fin_monomial_sum_ne_zero_iff {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)) ≠ 0 ↔ ∃ j, a j ≠ 0 :=
  Internal.fin_monomial_sum_ne_zero_iff a

end Algebraic.Cutwidth.Extractor
