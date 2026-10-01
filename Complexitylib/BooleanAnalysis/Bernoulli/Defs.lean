/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Finite Bernoulli coordinate sampling

Boolean masks represent coordinate sets. Product weights describe independent
coordinate inclusion with a common parameter, using finite real sums.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis

open scoped BigOperators

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
