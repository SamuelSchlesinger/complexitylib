/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Lossless.Mixture.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Lossless.Internal

/-!
# Flat lossless condensation by the actual runtime program

The decoded runtime condenser satisfies the checked GUV expansion guarantee
over the explicit binary field and extension. For every qualifying flat
source of equal-length bitstrings within the coefficient capacity, its
seeded output is close to a distribution uniform on equally many outputs
in each seed fiber. Every test retains the original seed coordinate.

A larger flat support is close to an explicit mixture of conditional
`K`-flat outputs. The error is the degree loss divided by the exact binary
field size; no error-below-one premise is needed. These finite results
combine Guruswami--Umans--Vadhan's polynomial expansion with the checked
uniform evaluator and explicit modulus construction. They concern uniform
finite supports, with parameter-growth bounds and extractor composition
remaining separate obligations.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual runtime map has a seedwise flat witness, with the GUV loss
normalized by the explicit field cardinality. The witness may depend on `P`;
the runtime map is fixed before the source support is chosen. -/
theorem decodedCondenser_flat_lossless (s v n : Nat)
    [Fintype (AdjoinRoot (binaryModulus s))]
    (halfDegree extensionCount stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v)
    (degree : 0 < v) (fieldSize : stride.length ≤ 2 * 3 ^ s)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v)
    (P : Finset (List Bool)) (nonempty : P.Nonempty)
    (source : ∀ bits ∈ P, bits.length = n)
    (size : P.card ≤ (2 ^ stride.length) ^ count.length) :
    ∃ g : AdjoinRoot (binaryModulus s) →
        (P ↪ (Fin count.length → AdjoinRoot (binaryModulus s))),
      ∀ T : Finset (AdjoinRoot (binaryModulus s) ×
          (Fin count.length → AdjoinRoot (binaryModulus s))),
        |seededTestProb
            (fun bits : P => decodedCondenser s halfDegree extensionCount stride count bits.val) T -
          seededTestProb (fun bits y => g y bits) T| ≤
            (((3 ^ v - 1) * (2 ^ stride.length - 1) * count.length : Nat) : ℝ) /
              (2 : ℝ) ^ (2 * 3 ^ s) :=
  Internal.decodedCondenser_flat_lossless s v n halfDegree extensionCount stride count
    half extension degree fieldSize capacity P nonempty source size

open scoped Classical in
/-- Above the threshold, the actual runtime map is close to an explicit
mixture of seedwise `K`-flat witnesses. Only `K` must fit the output capacity. -/
theorem decodedCondenser_flat_mixture (s v n : Nat)
    [Fintype (AdjoinRoot (binaryModulus s))]
    (halfDegree extensionCount stride count : List Bool)
    (half : halfDegree.length = 3 ^ s) (extension : extensionCount.length = 3 ^ v)
    (degree : 0 < v) (fieldSize : stride.length ≤ 2 * 3 ^ s)
    (capacity : n ≤ (2 * 3 ^ s) * 3 ^ v)
    (P : Finset (List Bool)) (source : ∀ bits ∈ P, bits.length = n) {K : Nat}
    (positive : 0 < K) (threshold : K ≤ P.card)
    (size : K ≤ (2 ^ stride.length) ^ count.length) :
    ∃ g : ∀ S : P.powersetCard K, AdjoinRoot (binaryModulus s) →
        (S.val ↪ (Fin count.length → AdjoinRoot (binaryModulus s))),
      ∀ T : Finset (AdjoinRoot (binaryModulus s) ×
          (Fin count.length → AdjoinRoot (binaryModulus s))),
        |seededTestProb
            (fun bits : P => decodedCondenser s halfDegree extensionCount stride count bits.val) T -
          seededMixtureTestProb (fun _ : P.powersetCard K =>
            ((P.powersetCard K).card : ℝ)⁻¹) (fun S bits y => g S y bits) T| ≤
            (((3 ^ v - 1) * (2 ^ stride.length - 1) * count.length : Nat) : ℝ) /
              (2 : ℝ) ^ (2 * 3 ^ s) :=
  Internal.decodedCondenser_flat_mixture s v n halfDegree extensionCount stride count
    half extension degree fieldSize capacity P source positive threshold size

end Algebraic.Cutwidth.Extractor
