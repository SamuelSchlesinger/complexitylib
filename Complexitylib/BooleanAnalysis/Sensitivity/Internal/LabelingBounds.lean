/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith

/-!
# Sensitivity separation: labeling bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sensitivity/LabelingBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis.Sensitivity

/- Symbolic estimates for the sixteen-vertex labeling union bound. -/

namespace Internal

theorem le_ceil_sqrt_sq (M : ℕ) : M ≤ (Nat.ceil (Real.sqrt M))^2 := by
  have hs := Nat.le_ceil (Real.sqrt (M : ℝ))
  have hr := Real.sqrt_nonneg (M : ℝ)
  have he := Real.sq_sqrt (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hh : (M : ℝ) ≤ (Nat.ceil (Real.sqrt M) : ℝ)^2 := by nlinarith
  exact_mod_cast hh

theorem labeling_space_large {M : ℕ} (hM : 3 ≤ M) :
    120 ≤ (2*M^2+1)*(2*M^2+1) := by
  have : 19 ≤ 2*M^2+1 := by nlinarith
  nlinarith

end Internal

end Complexity.BooleanAnalysis.Sensitivity
