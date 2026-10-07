/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HardSlice
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CircuitQuantitative

/-!
# Unrestricted depth-three lower bound: language lower bound

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/LanguageLowerBound.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound

theorem language_depth_three_gate_lower_bound (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit3 (Fin n),
      C.Computes (fun x => language (List.ofFn x)) →
      (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) < (C.gateCount : ℝ) := by
  have hs : 0 ≤ 3 * A := mul_nonneg (by norm_num) hA.le
  obtain ⟨N, hN, hslice⟩ := exists_language_slice_small_correlations (3 * A) hs
  refine ⟨N, ?_⟩
  intro n hn C hC
  have hnlarge : 20480 ≤ n := hN.trans hn
  have hd : 4 ≤ dataDimension n := by
    unfold dataDimension
    omega
  obtain ⟨α, hα⟩ := hslice n hn
  have hrestricted := circuit_lower_bound_of_small_cnf_correlations
    (dataDimension n) (degreeCutoff (3 * A) (dataDimension n))
    (3 * A) hs hd (degreeCutoff_lower (3 * A) (dataDimension n))
    (fun x => language (List.ofFn (GateInput.assignment α x))) hα
    (C.subst α) (C.computes_subst hC α)
  have hdata : (2 : ℝ) ^ ((3 * A) * Real.sqrt (dataDimension n : ℝ)) <
      (C.gateCount : ℝ) := by
    simpa only [Circuit3.gateCount_subst] using hrestricted
  exact (circuit_size_scale A hA.le n (by omega)).trans_lt hdata

end DepthThreeLowerBound

end Complexity
