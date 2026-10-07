/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Main
public import Complexitylib.Circuits.DepthThree.LowerBound.ThresholdWeight
public import Complexitylib.Circuits.DepthThree.LowerBound.Uniform
public import Complexitylib.Circuits.DepthThree.LowerBound.NormalForm
public import Complexitylib.Circuits.DepthThree.LowerBound.Cslib

/-!
# Beyond the square-root exponent for unrestricted depth-three circuits

OpenAI, *Beyond the Square-Root Exponent for Depth-Three Boolean Circuits*
(23 September 2026):
https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Beyond-the-Square-Root-Exponent-for-Depth-Three-Boolean-Circuits-September-23-2026

An explicit language has a finite multitape polynomial-time decider, but every
OR-AND-OR circuit computing its length-`n` slice needs more than `2 ^ (A * sqrt n)`
gates, eventually for every fixed `A > 0`. Bottom fan-in is unrestricted.
Literals and constants are free; lower gates may be shared.

The machine and circuit models are those in `LowerBound.Defs`. In particular,
this statement supplies an actual finite multitape decider and its time bound;
`LowerBound.Uniform` also establishes membership in complexitylib's canonical `P`.
`LowerBound.Cslib` transfers balanced hardness to general depth-three CSLib circuits.
-/

public section

namespace Complexity.DepthThreeLowerBound

/-- The imported unrestricted depth-three lower bound, including the explicit
finite multitape polynomial-time witness. -/
theorem exists_polynomial_time_language_depth_three_lower_bound :
    ∃ (L : List Bool → Bool) (M : FiniteMultiTapeMachine) (C a : ℕ),
      0 < C ∧ 0 < a ∧
      (∀ w : List Bool, MultiTapeHaltsIn M w (L w) (C * (w.length + 1) ^ a)) ∧
      ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Circuit3 (Fin n), D.Computes (fun x => L (List.ofFn x)) →
          (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (D.gateCount : ℝ) :=
  exists_polynomial_time_language_depth_three_lower_bound_proof

end Complexity.DepthThreeLowerBound
