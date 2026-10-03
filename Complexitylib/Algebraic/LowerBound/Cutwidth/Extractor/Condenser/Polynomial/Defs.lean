/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Polynomial.Div

/-!
# Polynomial map for the linear GUV condenser

The source polynomial is repeatedly squared modulo a supplied polynomial.
Evaluating every `r`th iterate gives the Parvaresh--Vardy neighbor map with
exponent `h = 2^r`, omitting the seed coordinate. This is the map in
Guruswami, Umans, and Vadhan (2009), Section 3.1, with the characteristic-power
choice used by Cheraghchi (2010), Section 2.3.3, to obtain source linearity.

These definitions use Mathlib's noncomputable polynomial representation.
They specify the algebraic map and its modular iteration. `Condenser.Encoding`
and its correctness layer implement this map for the explicit binary fields;
the expansion and flat lossless bounds are proved in separate condenser modules.
No basis or irreducible polynomial is chosen in these general definitions.
For a nonmonic modulus, Mathlib's `%ₘ` leaves the dividend unchanged; the
degree guarantee requires monicity, and the eventual expansion proof also
needs the construction's irreducibility hypotheses.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Repeated modular squaring, starting with the reduced source polynomial.
For monic `E`, every stored polynomial has degree less than `E.degree`. -/
noncomputable def modularFrobenius {F : Type*} [CommRing F]
    (E : Polynomial F) : Nat → Polynomial F → Polynomial F
  | 0, f => f %ₘ E
  | j + 1, f => (modularFrobenius E j f) ^ 2 %ₘ E

/-- The polynomial output coordinates of the GUV map for exponent `2^r`.
The seed `y` is not included in the output, matching the strong condenser
convention. On source polynomials of degree less than a monic `E`, coordinate
zero is `f.eval y`. -/
noncomputable def polynomialCondenser {F : Type*} [CommRing F]
    (E : Polynomial F) (r m : Nat) (f : Polynomial F) (y : F) : Fin m → F :=
  fun i => (modularFrobenius E (r * i.val) f).eval y

end Algebraic.Cutwidth.Extractor
