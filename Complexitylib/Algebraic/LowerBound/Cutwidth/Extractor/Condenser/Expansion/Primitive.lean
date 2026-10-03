/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.BigOperators.Field
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Primitive.Internal

/-!
# Primitive interpolation coefficients for condenser expansion

A nonzero interpolating family can be divided by common factors of a supplied
monic modulus until at least one coefficient is nonzero modulo that modulus.
Its degree bounds and vanishing constraints are preserved when the modulus
has no zero at the constrained seeds.

This proves the normalization step in Guruswami, Umans, and Vadhan,
*Unbalanced Expanders and Randomness Extractors from Parvaresh--Vardy Codes*
(2009), Theorem 3.3:
https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf.
The no-zero hypothesis holds for irreducible
moduli of degree at least two; degree-one moduli need a separate expansion
argument. This is an algebraic witness proof, not a condenser evaluator.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Remove common modulus factors without increasing coefficient degrees or
changing the zero constraints. The resulting family has a coefficient not
divisible by `E`, hence a nonzero coefficient in the quotient by `E`. -/
theorem exists_primitive_polynomialFamily {F X : Type*} [Field F] {A K : Nat}
    (E : Polynomial F) (monic : E.Monic) (positive : 0 < E.natDegree)
    (T : Finset X) (seed : X → F) (weight : X → Fin K → F)
    (nonvanishing : ∀ x ∈ T, E.eval (seed x) ≠ 0)
    (p : Fin K → Polynomial F) (nonzero : p ≠ 0)
    (degree : ∀ j, (p j).degree < A)
    (vanish : ∀ x ∈ T, ∑ j, (p j).eval (seed x) * weight x j = 0) :
    ∃ q : Fin K → Polynomial F, q ≠ 0 ∧
      (∀ j, (q j).degree < A) ∧
      (∀ x ∈ T, ∑ j, (q j).eval (seed x) * weight x j = 0) ∧
      ∃ j, ¬ E ∣ q j :=
  Internal.exists_primitive_polynomialFamily E monic positive T seed weight nonvanishing
    p nonzero degree vanish

end Algebraic.Cutwidth.Extractor
