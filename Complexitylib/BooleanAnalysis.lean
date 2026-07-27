/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.BooleanAnalysis.FourierExpansion

/-!
# Analysis of Boolean functions

Aggregation module for the Fourier analysis of Boolean functions, following Ryan
O'Donnell's *Analysis of Boolean Functions*. This subtheory grows inside the
larger complexity-theory corpus, where the Fourier-analytic toolkit underpins
circuit lower bounds (small-depth circuits, `AC⁰`), learning, property testing,
and the natural-proofs barrier.

Currently formalized: Chapter 1 — Boolean functions and the Fourier expansion
(`Complexitylib.BooleanAnalysis.FourierExpansion`), with the parity functions as
an orthonormal basis, Fourier coefficients and weights, Parseval/Plancherel, and
the mean/variance/covariance and convolution API. All definitions and theorems
live under the `Complexity.BooleanAnalysis` namespace.
-/

@[expose] public section
