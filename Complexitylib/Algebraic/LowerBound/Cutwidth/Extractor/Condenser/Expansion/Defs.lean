/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic

/-!
# The seeded polynomial neighbor graph

The Guruswami--Umans--Vadhan graph retains the seed and evaluates the first
`m` source powers with exponents `h^i`, reduced modulo a supplied polynomial.
The graph is defined for arbitrary `h`; the characteristic-power choice gives
the linear condenser map. These semantic definitions do not choose a field,
choose a modulus, or supply an encoded evaluator.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical

/-- A seeded neighbor in the polynomial graph of GUV (2009), Section 3.1. -/
noncomputable def polynomialNeighbor {F : Type*} [CommRing F]
    (E : Polynomial F) (h m : Nat) (f : Polynomial F) (y : F) : F × (Fin m → F) :=
  (y, fun i => (f ^ (h ^ i.val) %ₘ E).eval y)

/-- All seeded polynomial neighbors reached from a finite source set. -/
noncomputable def polynomialNeighborSet {F : Type*} [CommRing F] [Fintype F]
    (E : Polynomial F) (h m : Nat) (P : Finset (Polynomial F)) :
    Finset (F × (Fin m → F)) :=
  P.biUnion fun f => Finset.univ.image (polynomialNeighbor E h m f)

end Algebraic.Cutwidth.Extractor
