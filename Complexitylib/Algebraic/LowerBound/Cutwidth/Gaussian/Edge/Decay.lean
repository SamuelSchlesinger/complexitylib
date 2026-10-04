/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Decay.Internal

/-!
# Threshold decay of Gaussian crossings

A threshold `t` separates two unit Gaussian forms with correlation `ρ` with probability at
most `exp (-t²/2) · arccos ρ / π`. This multiplies Sheppard's bound
`gaussPi_between_le_arccos` by the Gaussian factor `exp (-t²/2)`, so thresholds far from
the median are crossed rarely.

* `prod_gaussianReal_abs_sub_le_abs_exp`: for independent centered Gaussians `X` and `Y` of
  variances `s > 0` and `r`, the event `|X - c| ≤ |Y|` has probability at most
  `(2/π) arctan (√r / √s) exp (-c² / (2 (s + r)))`. In polar coordinates the event occupies,
  at each radius `R`, at most two arcs of total length `4 arctan (√r / √s)`, and none when
  `R < |c| / √(s + r)`; the radial tail beyond that radius carries the factor
  `exp (-c² / (2 (s + r)))`.
* `gaussPi_between_le_arctan_exp`: for coefficient vectors of equal norm with nonzero sum, a
  threshold `t` separates the two forms with probability at most
  `(2/π) arctan (‖β - α‖ / ‖α + β‖) exp (-t² / (2 ‖α‖²))`. The forms `form (α + β)` and
  `form (β - α)` are independent, and a crossing forces the first to lie within the
  absolute value of the second around `2t`.
* `gaussPi_between_le_exp_arccos`: the bound `exp (-t²/2) arccos ρ / π` for unit forms.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **Decay of the crossing event.** For independent centered Gaussians `X` and `Y` of
variances `s > 0` and `r`, the event `|X - c| ≤ |Y|` has probability at most
`(2/π) arctan (√r / √s) exp (-c² / (2 (s + r)))`. -/
theorem prod_gaussianReal_abs_sub_le_abs_exp (s r : ℝ≥0) (hs : s ≠ 0) (c : ℝ) :
    ((gaussianReal 0 s).prod (gaussianReal 0 r)) {p : ℝ × ℝ | |p.1 - c| ≤ |p.2|} ≤
      ENNReal.ofReal (2 / Real.pi * Real.arctan (Real.sqrt r / Real.sqrt s) *
        Real.exp (-(c ^ 2) / (2 * ((s : ℝ) + r)))) :=
  Internal.prod_gaussianReal_abs_sub_le_abs_exp s r hs c

/-- **Threshold decay of crossings.** For coefficient vectors of equal norm with nonzero
sum, a threshold `t` separates the two Gaussian forms with probability at most
`(2/π) arctan (‖β - α‖ / ‖α + β‖) exp (-t² / (2 ‖α‖²))`. -/
theorem gaussPi_between_le_arctan_exp {ι : Type} [Fintype ι] (α β : ι → ℝ)
    (hnorm : ∑ i, α i ^ 2 = ∑ i, β i ^ 2) (hsum : 0 < ∑ i, (α i + β i) ^ 2) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      2 / Real.pi *
          Real.arctan (Real.sqrt (∑ i, (β i - α i) ^ 2) / Real.sqrt (∑ i, (α i + β i) ^ 2)) *
        Real.exp (-(t ^ 2) / (2 * ∑ i, α i ^ 2)) :=
  Internal.gaussPi_between_le_arctan_exp α β hnorm hsum t

/-- **Threshold decay of crossings for unit forms.** A threshold `t` separates two unit
Gaussian forms of correlation `ρ` with probability at most `exp (-t²/2) arccos ρ / π`. -/
theorem gaussPi_between_le_exp_arccos {ι : Type} [Fintype ι] {α β : ι → ℝ}
    (hα : ∑ i, α i ^ 2 = 1) (hβ : ∑ i, β i ^ 2 = 1) (hx : -1 < ∑ i, α i * β i) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      Real.exp (-(t ^ 2) / 2) * (Real.arccos (∑ i, α i * β i) / Real.pi) :=
  Internal.gaussPi_between_le_exp_arccos hα hβ hx t

end Algebraic.Cutwidth.Gaussian
