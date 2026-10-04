/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Expansion.Internal

/-!
# Expansion of the supplied polynomial neighbor graph

Every source set of size at most `h^m` expands by the field cardinality minus
`(E.natDegree - 1) * (h - 1) * m`. The interpolation and root-count proof uses
the actual source size throughout, so the bound holds for every smaller set.
This is the finite expansion argument of Guruswami, Umans, and Vadhan (2009),
Section 3.1, Theorem 3.3:
https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf.

The interpolation proof assumes the supplied modulus has degree at least two.
For degree-one moduli and a nonempty coordinate tuple, a separate count gives
exactly one field's worth of neighbors per source. `Lossless.Polynomial`
supplies the flat-source distributional consequence. Uniform field and modulus
selection and the encoded evaluator are in `Encoding.Explicit`; flat lossless
witnesses extend to capped weighted sources by
`weightedStrongSeededCondenser_of_flat_injections`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- For exponent `2^r`, the full neighbor is the seed paired with the checked
modular-squaring condenser output. -/
theorem polynomialNeighbor_pow_two {F : Type*} [CommRing F]
    (E : Polynomial F) (r m : Nat) (f : Polynomial F) (y : F) :
    polynomialNeighbor E (2 ^ r) m f y = (y, polynomialCondenser E r m f y) :=
  Internal.polynomialNeighbor_pow_two E r m f y

/-- For a degree-one modulus, bounded-degree sources are constants. The first
output coordinate distinguishes sources, and the retained seed distinguishes
all field-many neighbors of each source. -/
theorem card_polynomialNeighborSet_of_degree_one {F : Type*} [Field F] [Fintype F]
    (E : Polynomial F) (monic : E.Monic) (degree : E.natDegree = 1)
    (h m : Nat) (P : Finset (Polynomial F))
    (source : ∀ f ∈ P, f.degree < E.degree) :
    (polynomialNeighborSet E h (m + 1) P).card = Fintype.card F * P.card :=
  Internal.card_polynomialNeighborSet_of_degree_one E monic degree h m P source

/-- Any expansion factor whose degree budget fits inside the field size is
valid for every bounded-degree source set of size at most `h^m`. -/
theorem le_card_polynomialNeighborSet {F : Type*} [Field F] [Fintype F]
    {A h m : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree) (base : 0 < h)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (size : P.card ≤ h ^ m)
    (budget : A + (E.natDegree - 1) * (h - 1) * m ≤ Fintype.card F) :
    A * P.card ≤ (polynomialNeighborSet E h m P).card :=
  Internal.le_card_polynomialNeighborSet E monic irreducible degree base P source size budget

/-- The GUV polynomial graph expands all sets up to `h^m`; a degree loss larger
than the field cardinality yields the valid, vacuous natural-subtraction bound. -/
theorem polynomialNeighborSet_expansion {F : Type*} [Field F] [Fintype F]
    {h m : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree) (base : 0 < h)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (size : P.card ≤ h ^ m) :
    (Fintype.card F - (E.natDegree - 1) * (h - 1) * m) * P.card ≤
      (polynomialNeighborSet E h m P).card :=
  Internal.polynomialNeighborSet_expansion E monic irreducible degree base P source size

end Algebraic.Cutwidth.Extractor
