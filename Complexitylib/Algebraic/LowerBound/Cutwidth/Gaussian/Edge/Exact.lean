/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Star.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Exact.Internal

/-!
# Sheppard's crossing bound

A threshold separates two unit Gaussian forms with correlation `ρ` with probability at
most `arccos ρ / π`. At threshold `0` this is Sheppard's formula for the probability that
two correlated Gaussians differ in sign; this file proves the inequality at every
threshold. It sharpens `gaussPi_between_le`, replacing the ratio
`y = ‖β - α‖ / ‖α + β‖` in its bound `(2/π) y` with `arctan y ≤ y`.

* `gaussPi_abs_le_mul_abs`: for independent standard Gaussians `Z₁` and `Z₂`, the event
  `|Z₁| ≤ k |Z₂|` has probability `(2/π) arctan k`.
* `gaussPi_between_le_arctan`: for coefficient vectors of equal norm with nonzero sum, a
  threshold separates the two forms with probability at most
  `(2/π) arctan (‖β - α‖ / ‖α + β‖)`. The forms `form (α + β)` and `form (β - α)` are
  independent, and a crossing forces the first to lie within the absolute value of the
  second around twice the threshold. A centered Gaussian gives a symmetric interval at
  least the mass of any translate, so the threshold may be taken to be zero, leaving the
  planar angle law.
* `two_mul_arctan_tanHalf`: `2 arctan (tanHalf x) = arccos x`.
* `gaussPi_between_le_arccos`: the bound `arccos ρ / π` for unit forms.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open MeasureTheory ProbabilityTheory

/-- **Planar angle law.** For independent standard Gaussians, `|Z₁| ≤ k |Z₂|` has
probability `(2/π) arctan k`. -/
theorem gaussPi_abs_le_mul_abs (k : ℝ) (hk : 0 ≤ k) :
    (gaussPi (Fin 2)).real {ω | |ω 0| ≤ k * |ω 1|} = 2 / Real.pi * Real.arctan k :=
  Internal.gaussPi_abs_le_mul_abs k hk

/-- **Sheppard's bound at every threshold.** For coefficient vectors of equal norm with
nonzero sum, a threshold separates the two Gaussian forms with probability at most
`(2/π) arctan (‖β - α‖ / ‖α + β‖)`. -/
theorem gaussPi_between_le_arctan {ι : Type} [Fintype ι] (α β : ι → ℝ)
    (hnorm : ∑ i, α i ^ 2 = ∑ i, β i ^ 2) (hsum : 0 < ∑ i, (α i + β i) ^ 2) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      2 / Real.pi *
        Real.arctan (Real.sqrt (∑ i, (β i - α i) ^ 2) / Real.sqrt (∑ i, (α i + β i) ^ 2)) :=
  Internal.gaussPi_between_le_arctan α β hnorm hsum t

/-- `2 arctan (tan (θ/2)) = θ` in the form `2 arctan (tanHalf x) = arccos x`. -/
theorem two_mul_arctan_tanHalf {x : ℝ} (hx : -1 < x) (hx1 : x ≤ 1) :
    2 * Real.arctan (tanHalf x) = Real.arccos x :=
  Internal.two_mul_arctan_tanHalf hx hx1

/-- **Sheppard's bound for unit forms.** A threshold separates two unit Gaussian forms
with probability at most `arccos ρ / π`, where `ρ` is their correlation. -/
theorem gaussPi_between_le_arccos {ι : Type} [Fintype ι] {α β : ι → ℝ}
    (hα : ∑ i, α i ^ 2 = 1) (hβ : ∑ i, β i ^ 2 = 1) (hx : -1 < ∑ i, α i * β i) (t : ℝ) :
    (gaussPi ι).real {ω | Between t (form α ω) (form β ω)} ≤
      Real.arccos (∑ i, α i * β i) / Real.pi :=
  Internal.gaussPi_between_le_arccos hα hβ hx t

end Algebraic.Cutwidth.Gaussian
