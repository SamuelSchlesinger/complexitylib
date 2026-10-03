/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Binomial moduli of power-of-three degree

The modulus `X^(3^s) - a` is determined by one supplied base-field element and
an exponent. A noncube coefficient makes it irreducible. This semantic family
does not choose a finite field, select a coefficient, or specify an encoded
polynomial evaluator.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- A binomial modulus whose degree is a power of three. -/
noncomputable def binomialModulus {F : Type*} [Ring F] (a : F) (s : Nat) : Polynomial F :=
  Polynomial.X ^ (3 ^ s) - Polynomial.C a

end Algebraic.Cutwidth.Extractor
