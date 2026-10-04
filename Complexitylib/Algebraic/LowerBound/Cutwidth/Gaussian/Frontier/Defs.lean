/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Gaussian frontier coefficient

`frontierCoefficient = (3/π)(√2 - 1)/√(5 + 2√2) ≈ 0.14137` is the pathwidth coefficient of
edge-score decompositions of cubic graphs built from Gaussian distance-kernel scores.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- The cubic pathwidth coefficient of the Gaussian edge-score decomposition,
`(3/π)(√2 - 1)/√(5 + 2√2)`. -/
noncomputable def frontierCoefficient : ℝ :=
  3 / Real.pi * ((Real.sqrt 2 - 1) / Real.sqrt (5 + 2 * Real.sqrt 2))

end Algebraic.Cutwidth.Gaussian
