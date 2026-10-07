/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Multilinearize

/-!
# Gotsman--Linial: influence of polynomial threshold functions

OpenAI, *Average Sensitivity of Polynomial Threshold Functions* (25 September 2026):
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Average-Sensitivity-of-Polynomial-Threshold-Functions-September-25-2026

The imported proof establishes the bound `8 * d * sqrt n` on average sensitivity.
The bridge identifies average sensitivity with complexitylib's Fourier total
influence. A checked multilinearization removes the source statement's
multilinearity hypothesis, so the public bound accepts any real polynomial.
The sign convention is `sign(0) = 1`, with no nonvanishing hypothesis.

The noise and Fourier-tail estimates below combine this bound with the library's
existing Fourier API. They are elementary consequences, not claims of new
research results or of the sharper dimension-free noise bound in the source paper.
-/

public section

namespace Complexity.BooleanAnalysis

variable {n d : ℕ}

/-- Sign-cube multilinearization does not increase total degree. -/
theorem signMultilinearize_totalDegree_le (p : MvPolynomial (Fin n) ℝ) :
    (signMultilinearize p).totalDegree ≤ p.totalDegree :=
  PolynomialThreshold.Internal.signMultilinearize_totalDegree_le p

/-- Reducing exponents modulo two preserves evaluation whenever all coordinates square to one. -/
theorem signMultilinearize_eval (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, x i ^ 2 = 1) :
    MvPolynomial.eval x (signMultilinearize p) = MvPolynomial.eval x p :=
  PolynomialThreshold.Internal.signMultilinearize_eval p x hx

/-- Multilinearization preserves the threshold, including its values at polynomial zeros. -/
theorem polynomialThreshold_signMultilinearize (p : MvPolynomial (Fin n) ℝ) :
    polynomialThreshold (signMultilinearize p) = polynomialThreshold p :=
  PolynomialThreshold.Internal.polynomialThreshold_signMultilinearize p

/-- A polynomial threshold always takes values in `{-1, 1}`. -/
theorem isBooleanValued_polynomialThreshold (p : MvPolynomial (Fin n) ℝ) :
    IsBooleanValued (polynomialThreshold p) :=
  PolynomialThreshold.Internal.polynomialThreshold_isBooleanValued p

/-- **Gotsman--Linial bound.** Every degree-`d` real polynomial threshold has
total influence at most `8 * d * sqrt n`. Dimensions and degrees may be zero. -/
theorem totalInfluence_polynomialThreshold_le (p : MvPolynomial (Fin n) ℝ)
    (hd : p.totalDegree ≤ d) :
    totalInfluence (polynomialThreshold p) ≤ 8 * d * Real.sqrt n :=
  PolynomialThreshold.Internal.totalInfluence_polynomialThreshold_le p hd

/-- The influence bound in terms of the represented function and its threshold degree. -/
theorem IsPolynomialThreshold.totalInfluence_le {f : BooleanFunction n}
    (hf : IsPolynomialThreshold f d) : totalInfluence f ≤ 8 * d * Real.sqrt n := by
  obtain ⟨p, hp, rfl⟩ := hf
  exact totalInfluence_polynomialThreshold_le p hp

/-- Degree bounds on a threshold imply the corresponding spectral noise bound.
Here `ρ` is the correlation parameter; the bit-flip rate is `(1 - ρ) / 2`. -/
theorem IsPolynomialThreshold.noiseSensitivity_le {f : BooleanFunction n}
    (hf : IsPolynomialThreshold f d) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    noiseSensitivity ρ f ≤ 4 * (1 - ρ) * d * Real.sqrt n := by
  calc
    _ ≤ (1 - ρ) / 2 * totalInfluence f := noiseSensitivity_le_influence hρ0 hρ1 f
    _ ≤ (1 - ρ) / 2 * (8 * d * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hf.totalInfluence_le (by positivity)
    _ = _ := by ring

/-- Above Fourier degree `m`, a degree-`d` polynomial threshold has total Fourier
weight at most `8 * d * sqrt n / (m + 1)`. -/
theorem IsPolynomialThreshold.fourierWeightAbove_le {f : BooleanFunction n}
    (hf : IsPolynomialThreshold f d) (m : ℕ) :
    fourierWeightAbove f m ≤ 8 * d * Real.sqrt n / (m + 1) :=
  (fourierWeightAbove_le_totalInfluence f m).trans
    (div_le_div_of_nonneg_right hf.totalInfluence_le (by positivity))

end Complexity.BooleanAnalysis
