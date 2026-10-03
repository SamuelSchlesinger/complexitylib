/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Substitution.Defs
public import Mathlib.RingTheory.AdjoinRoot
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Quotient.Internal

/-!
# The quotient-field root bound in GUV expansion

The first `K` interpolation monomials become powers with exponents below `K`
in the quotient by a supplied irreducible modulus. A coefficient not divisible
by the modulus makes this polynomial nonzero. It has fewer than `K` roots,
and distinct bounded-degree source polynomials give distinct quotient classes.

This is the final algebraic step of Guruswami, Umans, and Vadhan (2009),
Theorem 3.3:
https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf.
The quotient field here is used in the semantic proof. Its Mathlib instance
does not provide an encoded field representation or a uniform evaluator.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Evaluation of the quotient polynomial agrees with the class of the
substituted interpolation sum. The exponent cap retains the actual `K`. -/
theorem substitutedSum_quotient_eval {F : Type*} [Field F] {h K m : Nat}
    (E : Polynomial F) (monic : E.Monic) (bound : K ≤ h ^ m)
    (p : Fin K → Polynomial F) (f : Polynomial F) :
    (∑ j : Fin K, Polynomial.monomial j.val (AdjoinRoot.mk E (p j))).eval
        (AdjoinRoot.mk E f) = AdjoinRoot.mk E (substitutedSum E h m p f) :=
  Internal.substitutedSum_quotient_eval E monic bound p f

/-- A primitive coefficient family gives fewer than `K` distinct bounded-degree
source polynomials at which its quotient polynomial vanishes. -/
theorem card_lt_of_quotient_polynomial_roots {F : Type*} [Field F] {K : Nat}
    (E : Polynomial F) (monic : E.Monic) (irreducible : Irreducible E)
    (p : Fin K → Polynomial F) (primitive : ∃ j, ¬ E ∣ p j)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (roots : ∀ f ∈ P,
      (∑ j : Fin K, Polynomial.monomial j.val (AdjoinRoot.mk E (p j))).eval
        (AdjoinRoot.mk E f) = 0) : P.card < K :=
  Internal.card_lt_of_quotient_polynomial_roots E monic irreducible p primitive P source roots

end Algebraic.Cutwidth.Extractor
