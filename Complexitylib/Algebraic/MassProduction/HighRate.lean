/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.BooleanRecovery

/-!
# High-rate punctured-line recovery codes

`HighRate.existsHighRateLineCode` constructs a systematic code with exact
dimension `A^m - (A-1)^m`, for `A = 2^(blockWidth * dimension)` and field
width `blockWidth * m`. `HighRate.retainedDimension_hasRateOne` proves its
rate tends to one in an integer precision formulation with an explicit
cutoff. Packing loses at most one extra codeword; Boolean resource recovery
and uniqueness of scheduled resource incidences are proved separately.

These coding estimates feed the completed runtime lookup, scheduling,
routing, and circuit composition in `Algebraic.MassProduction.Nonuniform`.
The real-rate leading coefficient is stated by
`Algebraic.MassProduction.Nonuniform.realSharpMassProduction`.
-/

@[expose] public section
