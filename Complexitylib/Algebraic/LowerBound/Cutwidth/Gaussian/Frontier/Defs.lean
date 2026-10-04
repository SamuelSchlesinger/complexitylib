/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The Gaussian frontier coefficient

`frontierCoefficient = (3/(2π)) arccos ((1 + 2√2)/4) ≈ 0.14035` is the pathwidth coefficient
of edge-score decompositions of cubic graphs built from Gaussian distance-kernel scores.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- The cubic pathwidth coefficient of the Gaussian edge-score decomposition,
`(3/(2π)) arccos ((1 + 2√2)/4)`. -/
noncomputable def frontierCoefficient : ℝ :=
  3 / (2 * Real.pi) * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)

end Algebraic.Cutwidth.Gaussian
