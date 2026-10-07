/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.ThresholdWeight

/-!
# Exponential CNF threshold weight for the explicit hard language

This consequence combines OpenAI's hard-slice correlations with input
substitution and the elementary correlation-to-margin inequality. It bounds
total absolute coefficient weight for margin-one representations. A constant
bias can be included as a feature using the empty, identically true CNF.

Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HardSlice.lean

The width cutoff is `ceil (3 * (s + 1) * sqrt (n / 5))`. For every fixed
`s ≥ 0`, the bound holds at all sufficiently large input lengths, on the
full language. Coefficient weight is distinct from arbitrary-weight gate count.
-/

public section

namespace Complexity.DepthThreeLowerBound

open scoped BigOperators

/-- Every margin-one representation of the explicit language by CNF indicators
of the specified width has at least the stated exponential coefficient weight. -/
theorem language_threshold_weight (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → CNF (Fin n)) (a : J → ℝ),
        (∀ j, (H j).WidthAtMost (degreeCutoff s (dataDimension n))) →
        (∀ x, 1 ≤ sign (language (List.ofFn x)) * ∑ j, a j * indicator ((H j).eval x)) →
        (2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 ≤
          ∑ j, |a j| :=
  language_threshold_weight_proof s hs

/-- Integer threshold representations need exponential coefficient weight without
an assumed margin. Ties at zero accept. An integer bias can be a coefficient
of the empty CNF, and its absolute value then contributes to the weight. -/
theorem language_integer_threshold_weight (s : ℝ) (hs : 0 ≤ s) :
    ∃ N : ℕ, 20480 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (J : Type) [Fintype J] (H : J → CNF (Fin n)) (z : J → ℤ),
        (∀ j, (H j).WidthAtMost (degreeCutoff s (dataDimension n))) →
        (∀ x, language (List.ofFn x) =
          decide (0 ≤ ∑ j, z j * if (H j).eval x then (1 : ℤ) else 0)) →
        ((2 : ℝ) ^ (4 * (s + 1) * Real.sqrt (dataDimension n : ℝ)) / 6 - 1) / 2 ≤
          ∑ j, |(z j : ℝ)| :=
  language_integer_threshold_weight_proof s hs

end Complexity.DepthThreeLowerBound
