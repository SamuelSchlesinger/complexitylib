/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraQuotient
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Language

/-!
# Unrestricted depth-three lower bound: algebra language

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/AlgebraLanguage.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

namespace ParsedInput

/-- The polynomial quotient ring determined by the parsed modulus. -/
abbrev QuotientRing (q : ParsedInput) := AdjoinRoot q.modulus

instance quotientRingFintype (q : ParsedInput) : Fintype q.QuotientRing :=
  BinaryAlgebra.inputQuotientFintype
    (fun i => BinaryAlgebra.bitValue (q.polynomial i))

/-- The hashed input polynomial viewed in the quotient ring. -/
def quotientHash (q : ParsedInput) : q.QuotientRing :=
  AdjoinRoot.mk q.modulus q.hashPolynomial

/-- A parsed coefficient polynomial viewed in the quotient ring. -/
def quotientCoefficient (q : ParsedInput) (j : Fin q.coefficientCount) : q.QuotientRing :=
  AdjoinRoot.mk q.modulus (q.coefficientPolynomial j)

/-- Evaluate the coefficient polynomial at the hashed input in the quotient ring. -/
def quotientEvaluation (q : ParsedInput) : q.QuotientRing :=
  ∑ j : Fin q.coefficientCount, q.quotientCoefficient j * q.quotientHash ^ j.val

theorem quotientHash_eq_encode (q : ParsedInput) :
    q.quotientHash = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (BinaryHash.hashBool q.hashSeed q.data i)) := rfl

theorem quotientCoefficient_eq_encode (q : ParsedInput) (j : Fin q.coefficientCount) :
    q.quotientCoefficient j = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (q.coefficients j i)) := rfl

/-- Identify coefficient bit blocks with tuples of quotient-ring elements. -/
def coefficientBitsEquiv (q : ParsedInput) :
    (Fin q.ringDegree → Bool) ≃ q.QuotientRing :=
  (BinaryAlgebra.bitsEquivF2 (Fin q.ringDegree)).trans
    (BinaryAlgebra.coordinates
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))).toEquiv.symm

@[simp] theorem coefficientBitsEquiv_apply (q : ParsedInput)
    (v : Fin q.ringDegree → Bool) :
    q.coefficientBitsEquiv v = BinaryAlgebra.encode
      (fun i => BinaryAlgebra.bitValue (q.polynomial i))
      (fun i => BinaryAlgebra.bitValue (v i)) := rfl

theorem coefficientBitsEquiv_coefficient (q : ParsedInput)
    (j : Fin q.coefficientCount) :
    q.coefficientBitsEquiv (q.coefficients j) = q.quotientCoefficient j := rfl

@[simp] theorem quotientRing_card (q : ParsedInput) :
    Fintype.card q.QuotientRing = 2 ^ q.ringDegree :=
  BinaryAlgebra.bitQuotient_card q.polynomial

theorem quotientEvaluation_eq_mk (q : ParsedInput) :
    q.quotientEvaluation = AdjoinRoot.mk q.modulus q.evaluationPolynomial := by
  simp only [quotientEvaluation, evaluationPolynomial, quotientCoefficient, quotientHash,
    map_sum, map_mul, map_pow]

theorem representative_quotientEvaluation (q : ParsedInput) :
    BinaryAlgebra.quotientRepresentative q.modulus_monic q.quotientEvaluation =
      q.evaluationRemainder := by
  rw [quotientEvaluation_eq_mk, BinaryAlgebra.quotientRepresentative_mk]
  rfl

theorem degreeZero_quotientEvaluation (q : ParsedInput) :
    BinaryAlgebra.degreeZero q.modulus_monic q.quotientEvaluation =
      q.evaluationRemainder.coeff 0 := by
  rw [BinaryAlgebra.degreeZero_apply, representative_quotientEvaluation]

theorem quotient_degreeZero_one (q : ParsedInput) (hr : 0 < q.ringDegree) :
    BinaryAlgebra.degreeZero q.modulus_monic (1 : q.QuotientRing) = 1 := by
  apply BinaryAlgebra.degreeZero_one
  change 0 < (BinaryAlgebra.inputPolynomialBits q.polynomial).natDegree
  rw [BinaryAlgebra.inputPolynomialBits_natDegree]
  exact hr

theorem evaluate_eq_true_iff_degreeZero (q : ParsedInput) :
    q.evaluate = true ↔
      BinaryAlgebra.degreeZero q.modulus_monic q.quotientEvaluation = 0 := by
  rw [evaluate_eq_true_iff, degreeZero_quotientEvaluation]

end ParsedInput

theorem language_eq_true_iff_quotient (w : List Bool) :
    language w = true ↔ InputFits w ∧
      BinaryAlgebra.degreeZero (decodeInput w).modulus_monic
        (decodeInput w).quotientEvaluation = 0 := by
  rw [language_eq_true_iff, ParsedInput.degreeZero_quotientEvaluation]

end DepthThreeLowerBound

end

end Complexity
