/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Substitution.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Substitution.Internal

/-!
# The substituted interpolation polynomial has bounded degree

After replacing each coordinate by a source power reduced modulo a supplied
monic modulus, the interpolation polynomial has degree below
`A + (E.natDegree - 1) * (h - 1) * m`. Its evaluation is exactly the weighted
sum of feature values constrained by interpolation. These are the degree and
evaluation steps in Guruswami--Umans--Vadhan (2009), Section 3.1.

The modulus need not be irreducible for these statements. The source is any
polynomial: its degree is reduced before the monomials are substituted. The
subsequent root-count proof separately requires the appropriate field and
source-injectivity hypotheses.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Polynomial substitution followed by evaluation equals evaluation of the
weighted monomial features used by the interpolation constraints. -/
theorem substitutedSum_eval {F : Type*} [CommRing F] {K : Nat}
    (E : Polynomial F) (h m : Nat) (p : Fin K → Polynomial F) (f : Polynomial F) (y : F) :
    (substitutedSum E h m p f).eval y =
      ∑ j, (p j).eval y * digitMonomial h j.val
        (fun i : Fin m => (f ^ (h ^ i.val) %ₘ E).eval y) :=
  Internal.substitutedSum_eval E h m p f y

/-- Each reduced coordinate has degree at most `E.natDegree - 1`, so the
digit sum gives this uniform bound on the substituted polynomial. -/
theorem substitutedSum_natDegree_le {F : Type*} [CommRing F]
    {K A h m : Nat} (E : Polynomial F) (p : Fin K → Polynomial F) (f : Polynomial F)
    (monic : E.Monic) (base : 0 < h)
    (coeff : ∀ j, (p j).degree < A) :
    (substitutedSum E h m p f).natDegree ≤
      (A - 1) + (E.natDegree - 1) * (h - 1) * m :=
  Internal.substitutedSum_natDegree_le E p f monic base coeff

/-- The strict-degree form used to deduce a zero polynomial from many roots. -/
theorem substitutedSum_degree_lt {F : Type*} [CommRing F]
    {K A h m : Nat} (E : Polynomial F) (p : Fin K → Polynomial F) (f : Polynomial F)
    (monic : E.Monic) (positive : 0 < A) (base : 0 < h)
    (coeff : ∀ j, (p j).degree < A) :
    (substitutedSum E h m p f).degree <
      (A + (E.natDegree - 1) * (h - 1) * m : Nat) :=
  Internal.substitutedSum_degree_lt E p f monic positive base coeff

end Algebraic.Cutwidth.Extractor
