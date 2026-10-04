/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Gaussian cutwidth coefficient

`cutwidthCoefficient = (3/π)(3 - 2√2) ≈ 0.16384` is the prefix-cut coefficient
achieved by Gaussian distance-kernel layouts of cubic graphs, below the `1/6` of the
Monien–Preis and Fomin–Høie bounds.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- The cubic cutwidth coefficient of the Gaussian layout, `(3/π)(3 - 2√2)`. -/
noncomputable def cutwidthCoefficient : ℝ :=
  3 / Real.pi * (3 - 2 * Real.sqrt 2)

end Algebraic.Cutwidth.Gaussian
