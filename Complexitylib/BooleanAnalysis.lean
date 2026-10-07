/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli
public import Complexitylib.BooleanAnalysis.CoordinateSampling
public import Complexitylib.BooleanAnalysis.Fibers
public import Complexitylib.BooleanAnalysis.FourierExpansion
public import Complexitylib.BooleanAnalysis.HarmonicMean
public import Complexitylib.BooleanAnalysis.LightPatterns
public import Complexitylib.BooleanAnalysis.MirrorSets
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation
public import Complexitylib.BooleanAnalysis.PolynomialThreshold
public import Complexitylib.BooleanAnalysis.Sensitivity
public import Complexitylib.BooleanAnalysis.ThresholdWeight

/-!
# Analysis of Boolean functions

Aggregation module for the Fourier analysis of Boolean functions, following Ryan
O'Donnell's *Analysis of Boolean Functions*. This subtheory grows inside the
larger complexity-theory corpus, where the Fourier-analytic toolkit underpins
circuit lower bounds (small-depth circuits, `AC⁰`), learning, property testing,
and the natural-proofs barrier.

The polynomial-threshold development imports OpenAI's (2026) Gotsman--Linial
bound and transports it to total influence on the canonical cube. It includes
multilinearization for arbitrary real polynomials and spectral noise and tail bounds.
The sensitivity development imports OpenAI's superquadratic block-sensitivity
separation and derives lower bounds for exact finite decision-tree depth.

Currently formalized: Boolean functions and the Fourier expansion, with the
parity functions as an orthonormal basis, Fourier coefficients and weights,
Parseval/Plancherel, and the mean/variance/covariance and convolution API;
Chapter 2 foundations include noise stability, the noise operator, derivatives,
and coordinate and total influence. The polynomial correlation development proves
the exponential XOR-of-majorities bound of Chattopadhyay, Hatami, Lee, Lovett,
Tal, and Viola (2026), including its finite middle-band estimate.
The harmonic mean development proves Korten's (2026) variational formula,
transform properties, and biased-cube inequality (Lemmas 11--12 and Corollary 1).
Bernoulli transference then gives the improved light-patterns lemma (Lemma 10),
with its exact constants and marginal-probability pattern count. These supply
analytic prerequisites for his top-down parity lower bound. The coordinate-fiber
development proves the conditional entropy bound (Lemma 4) and its good-fiber
probability estimate. The conditional coordinate-sampling law and guided
distribution complete the improved mirror-set lemma, with explicit constants
`q = 32768*k*p` and reverse limit deficit `194*k`.
All definitions and theorems live under the
`Complexity.BooleanAnalysis` namespace.
-/
