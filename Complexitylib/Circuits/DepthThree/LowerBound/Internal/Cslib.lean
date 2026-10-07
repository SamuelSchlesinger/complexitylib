/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FormulaNormalization
public import Complexitylib.Circuits.DepthThree.LowerBound.Uniform
public import Complexitylib.Circuits.AC0.Normalization.Cslib
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The depth-three lower bound in CSLib's general circuit model

Normalize a CSLib circuit to a formula and then to the source three-layer circuit in one
of its polarities. Balanced hardness covers both. The polynomial size overhead is absorbed
by increasing the arbitrary constant in the square-root exponent.
-/

public section

namespace Complexity.DepthThreeLowerBound

open Filter

lemma eventually_nat_le_two_sqrt :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ≤ (2 : ℝ) ^ Real.sqrt (n : ℝ) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 2
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).comp_tendsto
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply eventually_atTop.mp
  filter_upwards [h.bound (by norm_num : (0 : ℝ) < 1)] with n hn
  simp only [Function.comp_apply, Real.norm_eq_abs, one_mul] at hn
  rw [Real.sq_sqrt (Nat.cast_nonneg n), abs_of_nonneg (Nat.cast_nonneg n),
    abs_of_pos (Real.exp_pos _)] at hn
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] using hn

lemma shallow_cost_absorbed (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : ℕ,
      (s : ℝ) ≤ (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) →
      (2 * (2 * ((n : ℝ) + s) + 1) ^ 4 + 1) ≤
        (2 : ℝ) ^ ((5 * (A + 1)) * Real.sqrt (n : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_nat_le_two_sqrt
  refine ⟨max N 121, fun n hn s hs => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn121 : (121 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hsqrt : 11 ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt hn121
    norm_num at h
    exact h
  let E : ℝ := (2 : ℝ) ^ ((A + 1) * Real.sqrt (n : ℝ))
  have hE0 : 0 ≤ E := by positivity
  have hsmall : (2 : ℝ) ^ Real.sqrt (n : ℝ) ≤ E := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hlarge : 1251 ≤ E := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hsqrt
    norm_num at h
    linarith
  have hnE : (n : ℝ) ≤ E := (hN n hnN).trans hsmall
  have hsE : (s : ℝ) ≤ E := hs.trans (Real.rpow_le_rpow_of_exponent_le
    (by norm_num) (by nlinarith [Real.sqrt_nonneg (n : ℝ)]))
  have hbase : 2 * ((n : ℝ) + s) + 1 ≤ 5 * E := by linarith
  have hp : (2 * ((n : ℝ) + s) + 1) ^ 4 ≤ (5 * E) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hbase 4
  have hE4 : 1 ≤ E ^ 4 := one_le_pow₀ (by linarith : 1 ≤ E)
  have hmul := mul_le_mul_of_nonneg_right hlarge (by positivity : 0 ≤ E ^ 4)
  calc
    2 * (2 * ((n : ℝ) + s) + 1) ^ 4 + 1 ≤ 1251 * E ^ 4 := by nlinarith only [hp, hE4]
    _ ≤ E ^ 5 := by nlinarith only [hmul]
    _ = (2 : ℝ) ^ ((5 * (A + 1)) * Real.sqrt (n : ℝ)) := by
      dsimp [E]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring


lemma cslib_depth_three_source_proof {n : ℕ} [NeZero n]
    (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n 1) (hd : c.depth ≤ 3) :
    ∃ (b : Bool) (C : Circuit3 (Fin n)),
      C.gateCount ≤ 2 * (2 * (n + c.size) + 1) ^ 4 + 1 ∧
      C.Computes (fun x => Bool.xor (c.eval Basis.unboundedAndOr.interpretation x 0) b) := by
  obtain ⟨he, hdepth, hsize⟩ := CslibAC0.outputFormula_spec c
  obtain ⟨b, C, hC, hc⟩ := AC0Formula.depth_three_source_proof
    (CslibAC0.outputFormula c) (hdepth.trans hd)
  refine ⟨b, C, ?_, fun x => ?_⟩
  · have hpow := Nat.pow_le_pow_right (by lia : 0 < 2 * (n + c.size) + 1)
      (by lia : c.depth + 1 ≤ 4)
    have hb := hsize.trans hpow
    lia
  · exact (hc x).trans (congrArg (fun v => Bool.xor v b) (he x))

lemma balancedFamily_cslib_lower_bound_proof (A : ℝ) (hA : 0 < A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature (n + 1) 1,
        c.depth ≤ 3 →
        c.Computes Basis.unboundedAndOr.interpretation
          (Cslib.Circuits.single (balancedFamily n)) →
        (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) < (c.size : ℝ) := by
  obtain ⟨N, hN⟩ := balancedFamily_lower_bound (5 * (A + 1)) (by positivity)
  obtain ⟨K, hK⟩ := shallow_cost_absorbed A hA
  refine ⟨max N K, fun n hn c hd hc => ?_⟩
  by_contra hsmall
  have hs : (c.size : ℝ) ≤ (2 : ℝ) ^ (A * Real.sqrt (n + 1 : ℕ)) := le_of_not_gt hsmall
  obtain ⟨b, C, hC, hcomp⟩ := cslib_depth_three_source_proof c hd
  have hhard := hN n ((le_max_left _ _).trans hn) b C (fun x =>
    (hcomp x).trans (congrArg (fun v => Bool.xor v b) (congrFun (hc x) 0)))
  have hcount : (C.gateCount : ℝ) ≤ 2 * (2 * ((n + 1 : ℕ) + (c.size : ℝ)) + 1) ^ 4 + 1 := by
    exact_mod_cast hC
  have ha := hK (n + 1) (by have := (le_max_right _ _).trans hn; lia) c.size hs
  exact (not_lt_of_ge (hcount.trans ha)) hhard

end Complexity.DepthThreeLowerBound
