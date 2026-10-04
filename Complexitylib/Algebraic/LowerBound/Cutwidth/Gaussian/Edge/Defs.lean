/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Gaussian forms and threshold crossings

The sample space for the Gaussian vertex layout is `ι → ℝ` with independent
standard Gaussian coordinates. A coefficient vector `α` gives the score
`form α ω = ∑ i, α i * ω i`, and `Between t x y` says that the threshold `t`
separates the two scores `x` and `y`, with the lower one strictly below `t`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open MeasureTheory ProbabilityTheory

/-- The standard Gaussian product measure on `ι → ℝ`. -/
noncomputable abbrev gaussPi (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => gaussianReal 0 1

instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (gaussPi ι) := by
  unfold gaussPi; infer_instance

/-- The linear form `ω ↦ ∑ i, α i * ω i`. -/
noncomputable def form {ι : Type} [Fintype ι] (α : ι → ℝ) (ω : ι → ℝ) : ℝ :=
  ∑ i, α i * ω i

/-- `t` lies weakly above one value and strictly above the other. -/
def Between (t x y : ℝ) : Prop :=
  (x < t ∧ t ≤ y) ∨ (y < t ∧ t ≤ x)

end Algebraic.Cutwidth.Gaussian
