/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Polynomial.Internal

/-!
# Flat lossless condensation by the supplied polynomial map

For every qualifying nonempty flat source, the seeded output is close to a
distribution that is uniform on exactly the original number of source points
in every seed fiber. The comparison preserves the seed and bounds all tests
on the joint seed-output space. Its error is the GUV expansion loss divided
by the field cardinality.

For a larger flat source of size at least `K`, the same error bound holds
against an explicit mixture of seedwise `K`-flat witnesses, provided
`K ≤ (2^r)^m`. The original support may exceed the output alphabet size.

This is the flat-source distributional consequence of Guruswami--Umans--Vadhan
(2009), Theorem 3.3. The exponent `2^r` is the characteristic-power choice used
by Cheraghchi (2010) for source linearity. The field and modulus remain supplied;
this theorem provides neither their uniform construction nor an encoded
evaluator. General weighted sources require a separate decomposition argument.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Polynomial expansion gives a seed-preserving flat witness at the original
support size, with error equal to the normalized degree loss. The witness may
depend on the source; the condenser map itself is fixed. -/
theorem polynomialCondenser_flat_lossless {F : Type*} [Field F] [Fintype F]
    {r m : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree)
    (fieldSize : 2 ^ r ≤ Fintype.card F)
    (P : Finset (Polynomial F)) (nonempty : P.Nonempty)
    (source : ∀ f ∈ P, f.degree < E.degree) (size : P.card ≤ (2 ^ r) ^ m) :
    ∃ g : F → (P ↪ (Fin m → F)), ∀ T : Finset (F × (Fin m → F)),
      |seededTestProb (fun f : P => polynomialCondenser E r m f.val) T -
        seededTestProb (fun f y => g y f) T| ≤
          (((E.natDegree - 1) * (2 ^ r - 1) * m : Nat) : ℝ) / Fintype.card F :=
  Internal.polynomialCondenser_flat_lossless E monic irreducible degree fieldSize
    P nonempty source size

open scoped Classical in
/-- Every flat source above the threshold is close to an explicit mixture of
seedwise `K`-flat outputs. Only the threshold must fit in the output space. -/
theorem polynomialCondenser_flat_mixture {F : Type*} [Field F] [Fintype F]
    {r m K : Nat} (E : Polynomial F) (monic : E.Monic)
    (irreducible : Irreducible E) (degree : 1 < E.natDegree)
    (fieldSize : 2 ^ r ≤ Fintype.card F)
    (P : Finset (Polynomial F)) (source : ∀ f ∈ P, f.degree < E.degree)
    (positive : 0 < K) (threshold : K ≤ P.card) (capacity : K ≤ (2 ^ r) ^ m) :
    ∃ g : ∀ S : P.powersetCard K, F → (S.val ↪ (Fin m → F)),
      ∀ T : Finset (F × (Fin m → F)),
        |seededTestProb (fun f : P => polynomialCondenser E r m f.val) T -
          seededMixtureTestProb (fun _ : P.powersetCard K =>
            ((P.powersetCard K).card : ℝ)⁻¹)
            (fun S f y => g S y f) T| ≤
              (((E.natDegree - 1) * (2 ^ r - 1) * m : Nat) : ℝ) / Fintype.card F :=
  Internal.polynomialCondenser_flat_mixture E monic irreducible degree fieldSize
    P source positive threshold capacity

end Algebraic.Cutwidth.Extractor
