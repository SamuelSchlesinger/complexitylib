/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials.Defs
public import Mathlib.Algebra.Polynomial.Div

/-!
# Substituting a source polynomial into an interpolating family

For each base-`h` monomial, substitute the powers of the source polynomial
reduced modulo `E`, then multiply by its coefficient polynomial. The sum is
an ordinary polynomial in the seed variable. It is the witness to which the
first root-count argument in the GUV expansion proof applies.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Substitute the reduced source powers into all `K` interpolation monomials. -/
noncomputable def substitutedSum {F : Type*} [CommRing F] {K : Nat}
    (E : Polynomial F) (h m : Nat) (p : Fin K → Polynomial F) (f : Polynomial F) :
    Polynomial F :=
  ∑ j, p j * digitMonomial h j.val (fun i : Fin m => f ^ (h ^ i.val) %ₘ E)

end Algebraic.Cutwidth.Extractor
