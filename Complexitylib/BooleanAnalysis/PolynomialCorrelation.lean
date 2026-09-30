/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Bridge

/-!
# Exponential correlation bounds for polynomials

Theorem 1.1 of Eshan Chattopadhyay, Pooya Hatami, Chin Ho Lee, Shachar Lovett,
Avishay Tal, and Emanuele Viola, *Exponential Correlation Bounds for Polynomials*,
https://arxiv.org/abs/2609.28839 (v1, 23 September 2026).

For `k` disjoint blocks of odd length `ℓ = 2 * m + 1`, XOR of the block majorities
has absolute uniform correlation at most `(2 * d / sqrt ℓ)^k` with every
`MvPolynomial` over `ZMod 2` of total degree at most `d`. Both the set-of-true-bits
encoding and ordinary binary assignments are supported. The sharper finite
middle-band bound is included. The statements allow `k = 0` and `d = 0`.

The proof follows the paper's interpolation, modified-degree multiplication,
and agreement-set dimension argument. It uses filtered spans, so it does not
need uniqueness of the interpolation expansion. The paper's improved numerical
constant and its pseudorandom-generator applications are outside this development.
-/

public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation

variable {k m d r : ℕ}

/-- Interpolate any binary function on a cardinality downset using low monomials. -/
theorem low_interpolation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Low ι m → ZMod 2) :
    ∃ q ∈ lowSpan (ι := ι) m, ∀ x : Low ι m, q x.val = f x :=
  Internal.low_interpolation f

/-- The one-block interpolation decomposition used in Section 2.1 of the paper. -/
theorem majority_decomposition (f : Finset (Fin (2 * m + 1)) → ZMod 2) :
    ∃ q ∈ lowSpan m, ∃ r ∈ lowSpan m, f = q + fun x => majority x * r x :=
  Internal.majority_decomposition f

/-- **Multiplication lemma (Lemma 2.2).** Multiplication by a polynomial of
ordinary total degree at most `d` raises the modified-degree filtration by at most `d`. -/
theorem polynomial_mul_mem {f : BlockCube k m → ZMod 2} (hf : f ∈ filtration k m r)
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    (fun x => polynomialEval p x * f x) ∈ filtration k m (r + d) :=
  Internal.polynomial_mul_mem hf p hp

/-- The exact finite middle-band correlation estimate proved in Section 2.3. -/
theorem xorMajority_correlation_le_middleBand
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    correlation xorMajority (polynomialEval p) ≤
      (2 * (middleBandCount m d : ℝ) / 2 ^ (2 * m + 1)) ^ k :=
  Internal.correlation_middleBand_bound p hp

/-- **Theorem 1.1**, on inputs encoded by their true coordinates. -/
theorem xorMajority_correlation_le
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    correlation xorMajority (polynomialEval p) ≤ (2 * d / Real.sqrt (2 * m + 1)) ^ k :=
  Internal.correlation_sqrt_bound p hp

/-- **Theorem 1.1**, on ordinary binary assignments to the variables of `p`. -/
theorem xorMajorityBits_correlation_le
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) (hp : p.totalDegree ≤ d) :
    correlation xorMajorityBits (fun x => MvPolynomial.eval x p) ≤
      (2 * d / Real.sqrt (2 * m + 1)) ^ k :=
  Internal.correlation_bits_bound p hp

end Complexity.BooleanAnalysis.PolynomialCorrelation
