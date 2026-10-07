/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: asymptotic bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/AsymptoticBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open Filter
open scoped BigOperators Topology

namespace DepthThreeLowerBound

theorem exists_factorial_tail_width (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ b : ℕ, 1 ≤ b ∧ ∀ k : ℕ,
      (∑ ℓ ∈ Finset.Ico (b + 1) (k + 1), Q ^ ℓ / (ℓ.factorial : ℝ)) ≤ 1 / 2 := by
  let a : ℕ → ℝ := fun ℓ => Q ^ ℓ / (ℓ.factorial : ℝ)
  have ha : ∀ ℓ, 0 ≤ a ℓ := fun ℓ =>
    div_nonneg (pow_nonneg hQ ℓ) (Nat.cast_nonneg _)
  have hs : Summable a := Real.summable_pow_div_factorial Q
  have ht : Tendsto (fun n : ℕ => (∑' ℓ, a ℓ) - ∑ ℓ ∈ Finset.range n, a ℓ)
      atTop (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => ∑' ℓ, a ℓ) atTop (𝓝 (∑' ℓ, a ℓ)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hc.sub hs.hasSum.tendsto_sum_nat
  have he := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro k
  change (∑ ℓ ∈ Finset.Ico (max 1 N + 1) (k + 1), a ℓ) ≤ 1 / 2
  by_cases hk : max 1 N + 1 ≤ k + 1
  · rw [Finset.sum_Ico_eq_sub a hk]
    have hupper : (∑ ℓ ∈ Finset.range (k + 1), a ℓ) ≤ ∑' ℓ, a ℓ :=
      hs.sum_le_tsum _ (fun ℓ _ => ha ℓ)
    have htail := hN (max 1 N + 1)
      ((le_max_right 1 N).trans (Nat.le_succ _))
    exact (sub_le_sub_right hupper _).trans htail.le
  · rw [Finset.Ico_eq_empty_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hk)), Finset.sum_empty]
    norm_num

theorem div_five_ge (D n : ℕ) (h : 5 * D ≤ n) : D ≤ n / 5 := by
  omega

theorem input_div_five_scale (n : ℕ) (hn : 5 ≤ n) :
    0 < n / 5 ∧ n ≤ 9 * (n / 5) := by
  omega

theorem sqrt_input_div_five_le (n : ℕ) (hn : 5 ≤ n) :
    Real.sqrt (n : ℝ) ≤ 3 * Real.sqrt ((n / 5 : ℕ) : ℝ) := by
  have hscale : (n : ℝ) ≤ 9 * ((n / 5 : ℕ) : ℝ) := by
    exact_mod_cast (input_div_five_scale n hn).2
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg (n / 5) : (0 : ℝ) ≤ (n / 5 : ℕ))
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · nlinarith

theorem circuit_size_scale (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (hn : 5 ≤ n) :
    (2 : ℝ) ^ (A * Real.sqrt (n : ℝ)) ≤
      (2 : ℝ) ^ ((3 * A) * Real.sqrt ((n / 5 : ℕ) : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    A * Real.sqrt (n : ℝ) ≤ A * (3 * Real.sqrt ((n / 5 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_input_div_five_le n hn) hA
    _ = (3 * A) * Real.sqrt ((n / 5 : ℕ) : ℝ) := by ring

theorem final_error_exponents (s d S : ℝ) (hS0 : 0 ≤ S)
    (hS : S ≤ (2 : ℝ) ^ (s * Real.sqrt d)) (k : ℕ)
    (hk : 3 * (s + 1) * Real.sqrt d ≤ (k : ℝ)) :
    6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) +
        S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤
      6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) +
        (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := by
  have hfirst : 6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) ≤
      6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) := by
    calc
      6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) ≤
          6 * (2 : ℝ) ^ (s * Real.sqrt d) *
            (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by norm_num))
          (Real.rpow_nonneg (by norm_num) _)
      _ = 6 * ((2 : ℝ) ^ (s * Real.sqrt d) *
          (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16)) := by ring
      _ = 6 * (2 : ℝ) ^ (s * Real.sqrt d - (64 * (s + 1) * Real.sqrt d) / 16) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 2 ; ring
      _ = 6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) := by
        congr 2 ; ring
  have hSsq : S ^ 2 ≤ ((2 : ℝ) ^ (s * Real.sqrt d)) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hS hS hS0 (Real.rpow_nonneg (by norm_num) _)
  have hsecond : S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤
      (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := by
    calc
      S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤
          ((2 : ℝ) ^ (s * Real.sqrt d)) ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) :=
        mul_le_mul_of_nonneg_right hSsq (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ ((s * Real.sqrt d) * 2 + -(k : ℝ)) := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2) (s * Real.sqrt d) 2]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] ; norm_num
      _ ≤ (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [hk]
  exact add_le_add hfirst hsecond

theorem final_error_le (s d S : ℝ) (hs : 0 ≤ s) (hd : 4 ≤ d) (hS0 : 0 ≤ S)
    (hS : S ≤ (2 : ℝ) ^ (s * Real.sqrt d)) (k : ℕ)
    (hk : 3 * (s + 1) * Real.sqrt d ≤ (k : ℝ)) :
    6 * S * (2 : ℝ) ^ (-(64 * (s + 1) * Real.sqrt d) / 16) +
        S ^ 2 * (2 : ℝ) ^ (-(k : ℝ)) ≤ 5 / 128 := by
  have hroot : (2 : ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by norm_num; exact hd)
  have hprod : 0 ≤ s * Real.sqrt d := mul_nonneg hs (Real.sqrt_nonneg d)
  have hfirst : (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) ≤ (2 : ℝ) ^ (-8 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hsecond : (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) ≤ (2 : ℝ) ^ (-6 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  calc
    _ ≤ 6 * (2 : ℝ) ^ (-((3 * s + 4) * Real.sqrt d)) +
        (2 : ℝ) ^ (-((s + 3) * Real.sqrt d)) := final_error_exponents s d S hS0 hS k hk
    _ ≤ 6 * (2 : ℝ) ^ (-8 : ℝ) + (2 : ℝ) ^ (-6 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num)) hsecond
    _ = 5 / 128 := by norm_num

theorem correlation_error_le (s d : ℝ) (hs : 0 ≤ s) (hd : 1 ≤ d) :
    6 * (2 : ℝ) ^ (-(4 * (s + 1) * Real.sqrt d)) ≤ 3 / 8 := by
  have hroot : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd
  have hprod : 0 ≤ s * Real.sqrt d := mul_nonneg hs (Real.sqrt_nonneg d)
  have hp : (2 : ℝ) ^ (-(4 * (s + 1) * Real.sqrt d)) ≤ (2 : ℝ) ^ (-4 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  calc
    _ ≤ 6 * (2 : ℝ) ^ (-4 : ℝ) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 3 / 8 := by norm_num

end DepthThreeLowerBound

end

end Complexity
