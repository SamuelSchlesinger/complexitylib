/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Analysis.Real.Sqrt

/-!
# The crossing ratio

For unit vectors at angle `θ`, with inner product `x = cos θ`, the Gaussian threshold
crossing bound is proportional to `√(1 - x) / √(1 + x) = tan (θ / 2)`. This file names
that ratio as a function of the inner product.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- `tanHalf (cos θ) = tan (θ / 2)`: the crossing ratio `√(1 - x) / √(1 + x)`. -/
noncomputable def tanHalf (x : ℝ) : ℝ :=
  Real.sqrt (1 - x) / Real.sqrt (1 + x)

end Algebraic.Cutwidth.Gaussian
