/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: circuit density

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/CircuitDensity.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

theorem sign_eq_two_indicator_sub_one (b : Bool) :
    sign b = 2 * indicator b - 1 := by
  cases b <;> norm_num [sign, indicator]

theorem finiteAvg_sign (f : Cube V → Bool) :
    finiteAvg (fun x => sign (f x)) =
      2 * finiteAvg (fun x => indicator (f x)) - 1 := by
  calc
    _ = finiteAvg (fun x => 2 * indicator (f x) - 1) :=
      finiteAvg_congr (fun x => sign_eq_two_indicator_sub_one (f x))
    _ = _ := by rw [finiteAvg_sub, finiteAvg_const_mul, finiteAvg_const]

theorem acceptance_density_lower_of_sign_bound (f : Cube V → Bool) (ε : ℝ)
    (h : |finiteAvg (fun x => sign (f x))| ≤ ε) :
    (1 - ε) / 2 ≤ finiteAvg (fun x => indicator (f x)) := by
  have hl := (abs_le.mp h).1
  rw [finiteAvg_sign] at hl
  linarith

theorem acceptance_density_lower_of_width_correlation (f : Cube V → Bool)
    (k : ℕ) (ε : ℝ)
    (h : ∀ H : CNF V, H.WidthAtMost k →
      |finiteAvg (fun x : Cube V => sign (f x) * indicator (H.eval x))| ≤ ε) :
    (1 - ε) / 2 ≤ finiteAvg (fun x => indicator (f x)) := by
  apply acceptance_density_lower_of_sign_bound
  have he := h [] (by intro C hC; simp at hC)
  simpa using he

end DepthThreeLowerBound

end Complexity
