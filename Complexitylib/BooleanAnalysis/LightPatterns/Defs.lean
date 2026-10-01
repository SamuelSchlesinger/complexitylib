/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.Bernoulli.Defs

/-!
# Marginal probability masses on coordinate patterns

The marginal of a finite real-valued probability mass function is the sum of
its masses over all completions of a selected-coordinate pattern. This differs
from `coordinateMarginal`, which averages normalized densities.
-/

@[expose] public section

namespace Complexity.BooleanAnalysis

open scoped BigOperators

/-- Sum of the masses of all completions of a coordinate pattern. For a
nonnegative mass function summing to one, this is the probability of the pattern. -/
noncomputable def coordinateMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mass : (ι → Bool) → ℝ) (selected : ι → Bool)
    (pattern : {i // selected i = true} → Bool) : ℝ :=
  ∑ rest : {i // selected i ≠ true} → Bool,
    mass (fun i => if h : selected i = true then pattern ⟨i, h⟩ else rest ⟨i, h⟩)

end Complexity.BooleanAnalysis
