/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.LanguageParser
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AlgebraPolynomial
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Hash
public import Mathlib.Algebra.Polynomial.Div

/-!
# Unrestricted depth-three lower bound: language

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/Language.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

noncomputable section

open scoped BigOperators

namespace ParsedInput

/-- Pack the hashed data as a polynomial over the two-element field. -/
def hashPolynomial (q : ParsedInput) : Polynomial (ZMod 2) :=
  BinaryAlgebra.pack fun i =>
    BinaryAlgebra.bitValue (BinaryHash.hashBool q.hashSeed q.data i)

/-- Pack one parsed coefficient block as a binary polynomial. -/
def coefficientPolynomial (q : ParsedInput) (j : Fin q.coefficientCount) :
    Polynomial (ZMod 2) :=
  BinaryAlgebra.pack fun i => BinaryAlgebra.bitValue (q.coefficients j i)

/-- The monic modulus polynomial specified by the parsed input. -/
def modulus (q : ParsedInput) : Polynomial (ZMod 2) :=
  BinaryAlgebra.inputPolynomialBits q.polynomial

theorem modulus_monic (q : ParsedInput) : q.modulus.Monic :=
  BinaryAlgebra.inputPolynomialBits_monic q.polynomial

theorem modulus_degree (q : ParsedInput) :
    q.modulus.degree = (q.ringDegree : WithBot ℕ) :=
  BinaryAlgebra.inputPolynomialBits_degree q.polynomial

/-- Evaluate the parsed coefficient polynomial at the hash polynomial. -/
def evaluationPolynomial (q : ParsedInput) : Polynomial (ZMod 2) :=
  ∑ j : Fin q.coefficientCount,
    q.coefficientPolynomial j * q.hashPolynomial ^ j.val

/-- Reduce the evaluation polynomial modulo the parsed monic modulus. -/
def evaluationRemainder (q : ParsedInput) : Polynomial (ZMod 2) :=
  q.evaluationPolynomial %ₘ q.modulus

theorem evaluationRemainder_degree_lt (q : ParsedInput) :
    q.evaluationRemainder.degree < (q.ringDegree : WithBot ℕ) := by
  rw [evaluationRemainder, ← q.modulus_degree]
  exact Polynomial.degree_modByMonic_lt _ q.modulus_monic

/-- Accept when the constant coefficient of the evaluation remainder is zero. -/
def evaluate (q : ParsedInput) : Bool :=
  decide (q.evaluationRemainder.coeff 0 = 0)

theorem evaluate_eq_true_iff (q : ParsedInput) :
    q.evaluate = true ↔ q.evaluationRemainder.coeff 0 = 0 := by
  simp only [evaluate, decide_eq_true_eq]

end ParsedInput

/-- The explicit language: parse the input and test the constant coefficient of its remainder. -/
def language (w : List Bool) : Bool :=
  match parseInput w with
  | none => false
  | some q => q.evaluate

theorem language_of_not_fits {w : List Bool} (h : ¬InputFits w) :
    language w = false := by
  simp only [language, parseInput_of_not_fits h]

theorem language_of_fits {w : List Bool} (h : InputFits w) :
    language w = (decodeInput w).evaluate := by
  simp only [language, parseInput_of_fits h]

theorem language_eq_true_iff (w : List Bool) :
    language w = true ↔
      InputFits w ∧ (decodeInput w).evaluationRemainder.coeff 0 = 0 := by
  by_cases h : InputFits w
  · rw [language_of_fits h, ParsedInput.evaluate_eq_true_iff]
    simp only [h, true_and]
  · rw [language_of_not_fits h]
    simp only [Bool.false_eq_true, h, false_and]

end

end DepthThreeLowerBound

end Complexity
