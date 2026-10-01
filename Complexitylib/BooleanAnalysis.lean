/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.FourierExpansion
public import Complexitylib.BooleanAnalysis.HarmonicMean
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation

/-!
# Analysis of Boolean functions

Aggregation module for the Fourier analysis of Boolean functions, following Ryan
O'Donnell's *Analysis of Boolean Functions*. This subtheory grows inside the
larger complexity-theory corpus, where the Fourier-analytic toolkit underpins
circuit lower bounds (small-depth circuits, `AC⁰`), learning, property testing,
and the natural-proofs barrier.

Currently formalized: Boolean functions and the Fourier expansion, with the
parity functions as an orthonormal basis, Fourier coefficients and weights,
Parseval/Plancherel, and the mean/variance/covariance and convolution API;
Chapter 2 foundations include noise stability, the noise operator, derivatives,
and coordinate and total influence. The polynomial correlation development proves
the exponential XOR-of-majorities bound of Chattopadhyay, Hatami, Lee, Lovett,
Tal, and Viola (2026), including its finite middle-band estimate.
The harmonic mean development proves Korten's (2026) variational formula,
transform properties, and biased-cube inequality (Lemmas 11--12 and Corollary 1),
as a first layer toward his top-down parity lower bound.
All definitions and theorems live under the
`Complexity.BooleanAnalysis` namespace.
-/
