/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.FourierExpansion.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Polynomial threshold functions

A real polynomial is evaluated at the signs `chi (x i)` on the library's usual
cube. Its threshold is `1` at nonnegative values and `-1` at negative values.
In particular, zeros of the polynomial are allowed and have a fixed convention.

These definitions support the Gotsman--Linial bound proved in OpenAI's
*Average Sensitivity of Polynomial Threshold Functions* (25 September 2026).
The public degree predicate permits arbitrary polynomials, without requiring
that the input polynomial already be in multilinear normal form.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis

open scoped BigOperators

/-- Reduce every exponent modulo two, using the sign-cube relation `xᵢ² = 1`. -/
noncomputable def signMultilinearize {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ p.support,
    MvPolynomial.monomial (m.mapRange (fun k => k % 2) (by decide)) (p.coeff m)

/-- A polynomial threshold function on the sign cube, with `sign(0) = 1`. -/
noncomputable def polynomialThreshold {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    BooleanFunction n :=
  fun x => if 0 ≤ MvPolynomial.eval (fun i => chi (x i)) p then 1 else -1

/-- A Boolean function represented by a real polynomial threshold of degree at most `d`. -/
def IsPolynomialThreshold {n : ℕ} (f : BooleanFunction n) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ f = polynomialThreshold p

end Complexity.BooleanAnalysis
