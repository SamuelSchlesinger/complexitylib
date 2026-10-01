/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Pi

/-!
# Harmonic means and coordinate projections

Definitions for Section 4 of Oliver Korten, *Top-Down Lower Bounds for All
Depths*, ECCC TR26-221 (2026), https://eccc.weizmann.ac.il/report/2026/221/.

The harmonic mean is zero if any value is zero. This implements the paper's
extended-real convention without using the real-number convention `0⁻¹ = 0`
inside the average. Theorems assume nonnegative inputs.

A coordinate set is its Boolean membership function. Projections are represented
on the full cube: their value depends only on the selected coordinates. Averaging
on the full cube gives each projected pattern the same multiplicity, so this is
the uniform average over projected patterns. All expectations are finite sums.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis

open scoped BigOperators

/-- The uniform harmonic mean, with value zero whenever an entry is zero. -/
noncomputable def harmonicMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  if ∃ x, f x = 0 then 0 else (𝔼 x, (f x)⁻¹)⁻¹

/-- Average over the unselected coordinates, keeping the selected bits of `x`. -/
noncomputable def projectionAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected x : ι → Bool) : ℝ := by
  classical
  exact 𝔼 y : ι → Bool, f (fun i => if selected i then x i else y i)

/-- The marginal on actual selected-coordinate patterns, obtained by uniformly
averaging over their completions. For a normalized density `f`, this is the
normalized density of its coordinate projection. -/
noncomputable def coordinateMarginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected : ι → Bool)
    (pattern : {i // selected i = true} → Bool) : ℝ :=
  𝔼 rest : {i // selected i ≠ true} → Bool,
    f (fun i => if h : selected i = true then pattern ⟨i, h⟩ else rest ⟨i, h⟩)

/-- Korten's harmonic mean transform (Definition 5), represented on the full cube. -/
noncomputable def harmonicTransform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) : ℝ := by
  classical
  exact harmonicMean (projectionAverage f selected)

/-- Product Bernoulli weight of a coordinate set with inclusion parameter `p`. -/
noncomputable def bernoulliWeight {ι : Type*} [Fintype ι]
    (p : ℝ) (selected : ι → Bool) : ℝ :=
  ∏ i, if selected i then p else 1 - p

/-- Finite expectation over independently selected coordinates. It is a probability
expectation when `0 ≤ p ≤ 1`. -/
noncomputable def bernoulliAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (f : (ι → Bool) → ℝ) : ℝ := by
  classical
  exact ∑ selected, bernoulliWeight p selected * f selected

end Complexity.BooleanAnalysis
