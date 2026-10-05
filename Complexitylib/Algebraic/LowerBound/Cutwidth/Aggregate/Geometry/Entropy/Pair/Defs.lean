/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Local.Defs

/-!
# The entropy cost of an overlapping pair of conjunction features

The extremal four-outcome distribution is `(5/8, 1/8, 1/8, 1/8)`. Costs use
natural logarithms, consistently with `WeightBound`; divide by `Real.log 2`
to obtain bits. The saving compares this joint cost with two quarter-biased
marginal costs, rather than asserting a mutual-information lower bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

/-- Natural-log entropy of the extremal overlapping two-conjunction table. -/
noncomputable def pairEntropyCost : ℝ := 3 * Real.log 2 - (5 / 8) * Real.log 5

/-- The saving over separately charging two quarter-biased Boolean messages. -/
noncomputable def pairEntropySaving : ℝ := 2 * Real.binEntropy (1 / 4) - pairEntropyCost

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
