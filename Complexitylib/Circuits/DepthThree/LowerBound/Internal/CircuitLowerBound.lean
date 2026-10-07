/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CircuitNormalization
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.CircuitDeletion
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: circuit lower bound

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/CircuitLowerBound.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section
open scoped BigOperators

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [instFintypeV : Fintype V]

namespace CNF

theorem mass_le_of_width_correlation (H : CNF V) (hH : H.Normalized)
    (f : Cube V → Bool) (hsupport : ∀ x, H.eval x = true → f x = true)
    (k : ℕ) (ε : ℝ)
    (hcorr : ∀ J : CNF V, J.WidthAtMost k →
      |finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x))| ≤ ε) :
    finiteAvg (fun x : Cube V => indicator (H.eval x)) ≤
      ε + (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
  let J := H.deleteWide k
  have hpoint (x : Cube V) : indicator (H.eval x) ≤
      sign (f x) * indicator (J.eval x) +
        (indicator (J.eval x) - indicator (H.eval x)) := by
    have hm := H.indicator_eval_le_deleteWide k x
    have hs := hsupport x
    change indicator (H.eval x) ≤ indicator (J.eval x) at hm
    cases hh : H.eval x <;> cases hj : J.eval x <;> cases hf : f x <;>
      simp_all [indicator, sign]
  calc
    _ ≤ finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x) +
        (indicator (J.eval x) - indicator (H.eval x))) := finiteAvg_mono hpoint
    _ = finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x)) +
        finiteAvg (fun x : Cube V => indicator (J.eval x) - indicator (H.eval x)) :=
      finiteAvg_add _ _
    _ ≤ |finiteAvg (fun x : Cube V => sign (f x) * indicator (J.eval x))| +
        finiteAvg (fun x : Cube V => indicator (J.eval x) - indicator (H.eval x)) :=
      add_le_add_left (le_abs_self _) _
    _ ≤ ε + (H.length : ℝ) * ((2 : ℝ) ^ k)⁻¹ :=
      add_le_add (hcorr J (H.deleteWide_widthAtMost k)) (H.deletion_error_bound hH k)

end CNF

namespace Circuit3

omit [Fintype V] in
theorem indicator_output_le_sum_middle
    {V : Type uDepth1}

    (C : Circuit3 V) (x : Cube V) :
    indicator (C.eval x) ≤ ∑ j ∈ C.top, indicator ((C.middleCNF j).eval x) := by
  classical
  cases h : C.eval x with
  | false =>
    simpa using Finset.sum_nonneg (fun j (_ : j ∈ C.top) =>
      indicator_nonneg ((C.middleCNF j).eval x))
  | true =>
    obtain ⟨j, hj, hx⟩ := (C.eval_eq_true_iff_middleCNF x).mp h
    have hb := Finset.single_le_sum
      (fun i (_ : i ∈ C.top) => indicator_nonneg ((C.middleCNF i).eval x)) hj
    simpa [hx] using hb
theorem acceptance_density_le (C : Circuit3 V) (f : Cube V → Bool)
    (hC : C.Computes f) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hcorr : ∀ H : CNF V, H.WidthAtMost k →
      |finiteAvg (fun x : Cube V => sign (f x) * indicator (H.eval x))| ≤ ε) :
    finiteAvg (fun x : Cube V => indicator (f x)) ≤
      (C.gateCount : ℝ) * ε + (C.gateCount : ℝ) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := by
  classical
  let q : ℝ := ((2 : ℝ) ^ k)⁻¹
  have hq : 0 ≤ q := inv_nonneg.mpr (pow_nonneg (by norm_num) _)
  have hm (j : Fin C.middleCount) (hj : j ∈ C.top) :
      finiteAvg (fun x : Cube V => indicator ((C.middleCNF j).eval x)) ≤
        ε + (C.gateCount : ℝ) * q := by
    have hs (x : Cube V) (hx : (C.middleCNF j).eval x = true) : f x = true := by
      rw [← hC x]
      exact C.middleCNF_implies_output hj hx
    have hfirst := (C.middleCNF j).mass_le_of_width_correlation
      (C.middleCNF_normalized j) f hs k ε hcorr
    refine hfirst.trans (add_le_add_right (mul_le_mul_of_nonneg_right ?_ hq) ε)
    exact_mod_cast C.middleCNF_length_le_gateCount j
  have hB : 0 ≤ ε + (C.gateCount : ℝ) * q :=
    add_nonneg hε (mul_nonneg (Nat.cast_nonneg _) hq)
  calc
    _ = finiteAvg (fun x : Cube V => indicator (C.eval x)) :=
      finiteAvg_congr (fun x => congrArg indicator (hC x).symm)
    _ ≤ finiteAvg (fun x : Cube V =>
        ∑ j ∈ C.top, indicator ((C.middleCNF j).eval x)) :=
      finiteAvg_mono (C.indicator_output_le_sum_middle)
    _ = ∑ j ∈ C.top, finiteAvg (fun x : Cube V =>
        indicator ((C.middleCNF j).eval x)) := finiteAvg_sum _ _
    _ ≤ ∑ j ∈ C.top, (ε + (C.gateCount : ℝ) * q) :=
      Finset.sum_le_sum hm
    _ = (C.top.card : ℝ) * (ε + (C.gateCount : ℝ) * q) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C.gateCount : ℝ) * (ε + (C.gateCount : ℝ) * q) := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast C.top_card_le_gateCount
    _ = _ := by dsimp [q]; ring

end Circuit3

end DepthThreeLowerBound

end

end Complexity
