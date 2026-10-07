/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CircuitLowerBound
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CircuitDensity
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.AsymptoticBounds
public import Mathlib.Tactic.Convert

/-!
# Unrestricted depth-three lower bound: circuit quantitative

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/CircuitQuantitative.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

theorem circuit_lower_bound_of_small_cnf_correlations
    (d k : ℕ) (s : ℝ) (hs : 0 ≤ s) (hd : 4 ≤ d)
    (hk : 3 * (s + 1) * Real.sqrt (d : ℝ) ≤ (k : ℝ))
    (f : Cube (Fin d) → Bool)
    (hcorr : ∀ H : CNF (Fin d), H.WidthAtMost k →
      |finiteAvg (fun x : Cube (Fin d) => sign (f x) * indicator (H.eval x))| ≤
        6 * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16))
    (C : Circuit3 (Fin d)) (hC : C.Computes f) :
    (2 : ℝ) ^ (s * Real.sqrt (d : ℝ)) < (C.gateCount : ℝ) := by
  by_contra h
  have hsize : (C.gateCount : ℝ) ≤ (2 : ℝ) ^ (s * Real.sqrt (d : ℝ)) :=
    le_of_not_gt h
  let ε : ℝ := 6 * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16)
  have hε : 0 ≤ ε := mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have hdReal : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexponent : -(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16 =
      -(4 * (s + 1) * Real.sqrt (d : ℝ)) := by ring
  have hsmall : ε ≤ 3 / 8 := by
    dsimp only [ε]
    rw [hexponent]
    exact correlation_error_le s (d : ℝ) hs (by linarith)
  have hlower : (1 - ε) / 2 ≤
      finiteAvg (fun x : Cube (Fin d) => indicator (f x)) := by
    convert acceptance_density_lower_of_width_correlation f k ε
      (fun H hH => by convert hcorr H hH)
  have hupper : finiteAvg (fun x : Cube (Fin d) => indicator (f x)) ≤
      (C.gateCount : ℝ) * ε + (C.gateCount : ℝ) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := by
    convert C.acceptance_density_le f hC k ε hε
      (fun H hH => by convert hcorr H hH)
  have hinverse : (2 : ℝ) ^ (-(k : ℝ)) = ((2 : ℝ) ^ k)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hfinal := final_error_le s (d : ℝ) (C.gateCount : ℝ) hs hdReal
    (Nat.cast_nonneg _) hsize k hk
  have hupper' : finiteAvg (fun x : Cube (Fin d) => indicator (f x)) ≤ 5 / 128 := by
    calc
      _ ≤ (C.gateCount : ℝ) * ε + (C.gateCount : ℝ) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := hupper
      _ = 6 * (C.gateCount : ℝ) *
          (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt (d : ℝ)) / 16) +
          (C.gateCount : ℝ) ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) := by
        rw [hinverse]
        dsimp only [ε]
        ring
      _ ≤ 5 / 128 := hfinal
  linarith

end DepthThreeLowerBound

end Complexity
