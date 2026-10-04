/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Internal

/-!
# Threshold crossings of Gaussian forms

Three probability bounds for linear forms in independent standard Gaussians.

* `gaussPi_between_le`: for coefficient vectors `α` and `β` of equal norm,
  a threshold separates `form α` and `form β` with probability at most
  `(2/π) ‖β - α‖ / ‖α + β‖`. The forms `form (α + β)` and `form (β - α)` are
  independent Gaussians, and the crossing forces the first to lie within the
  absolute value of the second around twice the threshold. The bound
  multiplies the peak density of the first by the mean absolute value of the
  second.
* `gaussPi_window_le`: a unit form lands in a half-open window of width `δ`
  with probability at most `δ / √(2π)`, the peak density times the width.
* `gaussPi_tail_le`: Chebyshev's tail bound `1 / T²` for a unit form.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- A Gaussian form is a measurable function of the sample. -/
theorem measurable_form {ι : Type} [Fintype ι] (α : ι → ℝ) : Measurable (form α) :=
  Internal.measurable_form α

open MeasureTheory ProbabilityTheory

/-- **Threshold crossing.** For coefficient vectors of equal norm whose sum is
nonzero, the probability that a threshold separates the two Gaussian forms is at most
`(2/π) ‖β - α‖ / ‖α + β‖`. -/
theorem gaussPi_between_le {ι : Type} [Fintype ι] (α β : ι → ℝ)
    (hnorm : ∑ i, α i ^ 2 = ∑ i, β i ^ 2) (hsum : 0 < ∑ i, (α i + β i) ^ 2) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      2 / Real.pi * (Real.sqrt (∑ i, (β i - α i) ^ 2) / Real.sqrt (∑ i, (α i + β i) ^ 2)) :=
  Internal.gaussPi_between_le α β hnorm hsum t

/-- A unit Gaussian form lands in a window of width `δ` with probability at most
`δ / √(2π)`. -/
theorem gaussPi_window_le {ι : Type} [Fintype ι] (α : ι → ℝ) (hα : ∑ i, α i ^ 2 = 1)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (gaussPi ι).real {ω | s ≤ form α ω ∧ form α ω < s + δ} ≤ δ / Real.sqrt (2 * Real.pi) :=
  Internal.gaussPi_window_le α hα s hδ

/-- Chebyshev's tail bound for a unit Gaussian form. -/
theorem gaussPi_tail_le {ι : Type} [Fintype ι] (α : ι → ℝ) (hα : ∑ i, α i ^ 2 = 1)
    {T : ℝ} (hT : 0 < T) :
    (gaussPi ι).real {ω | T ≤ |form α ω|} ≤ 1 / T ^ 2 :=
  Internal.gaussPi_tail_le α hα hT

end Algebraic.Cutwidth.Gaussian
