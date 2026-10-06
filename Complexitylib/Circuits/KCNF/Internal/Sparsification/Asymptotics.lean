/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Internal.Sparsification.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Sparsification -- choosing the parameter

The number of leaves is at most `∑_{j ≤ ρ} (Λ choose j) ≤ exp (Λ / T) T ^ ρ` for every `T ≥ 1`
(`sum_choose_le_exp_mul_pow`), with `Λ = N k X ^ (2 k)` and `α ρ ≤ (k - 1) N`. Take
`T = M k X ^ (2 k)` with `1/M ≤ (ε/2) log 2`, so that `exp (Λ / T) ≤ 2 ^ (ε N / 2)`. Since `T` is
a polynomial in `α`, for `α` large `T ^ (k - 1) ≤ 2 ^ (ε α / 2)`, hence `T ^ ρ ≤ 2 ^ (ε N / 2)`.
-/

@[expose] public section

namespace Complexity.ClauseSet.Sparsify

open Finset Filter

variable {N : ℕ}

/-- **A binomial tail bound.** For every `T ≥ 1`, `∑_{j ≤ ρ} (Λ choose j) ≤ exp (Λ / T) T ^ ρ`. -/
theorem sum_choose_le_exp_mul_pow (Λ ρ T : ℕ) (hT : 1 ≤ T) :
    (∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ)) ≤ Real.exp (Λ / T) * (T : ℝ) ^ ρ := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set t : ℝ := 1 / T with ht
  have ht0 : 0 ≤ t := by positivity
  have hg : ∀ j, 0 ≤ (Λ.choose j : ℝ) * t ^ j := fun j => by positivity
  have hpartial : ∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ) * t ^ j ≤ (1 + t) ^ Λ := by
    set m := max (ρ + 1) (Λ + 1)
    calc ∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ) * t ^ j
        ≤ ∑ j ∈ range m, (Λ.choose j : ℝ) * t ^ j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (le_max_left _ _))
            fun j _ _ => hg j
      _ = ∑ j ∈ range (Λ + 1), (Λ.choose j : ℝ) * t ^ j := by
          refine (sum_subset (range_subset_range.mpr (le_max_right _ _)) fun j _ hj => ?_).symm
          rw [Nat.choose_eq_zero_of_lt (by simpa using hj), Nat.cast_zero, zero_mul]
      _ = (1 + t) ^ Λ := by
          rw [add_comm (1 : ℝ) t, add_pow]
          refine sum_congr rfl fun j _ => ?_
          rw [one_pow, mul_one, mul_comm]
  calc (∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ))
      ≤ ∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ) * t ^ j * (T : ℝ) ^ ρ := by
        refine sum_le_sum fun j hj => ?_
        have hjρ : j ≤ ρ := Nat.lt_succ_iff.mp (mem_range.mp hj)
        have : 1 ≤ t ^ j * (T : ℝ) ^ ρ := by
          rw [← Nat.add_sub_cancel' hjρ, pow_add, ← mul_assoc, ht, ← mul_pow, one_div,
            inv_mul_cancel₀ hT0.ne', one_pow, one_mul]
          exact one_le_pow₀ hT1
        calc (Λ.choose j : ℝ) = (Λ.choose j : ℝ) * 1 := (mul_one _).symm
          _ ≤ (Λ.choose j : ℝ) * (t ^ j * (T : ℝ) ^ ρ) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = (Λ.choose j : ℝ) * t ^ j * (T : ℝ) ^ ρ := by ring
    _ = (∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ) * t ^ j) * (T : ℝ) ^ ρ := by
        rw [sum_mul]
    _ ≤ (1 + t) ^ Λ * (T : ℝ) ^ ρ := by gcongr
    _ ≤ Real.exp t ^ Λ * (T : ℝ) ^ ρ := by
        gcongr
        linarith [Real.add_one_le_exp t]
    _ = Real.exp (Λ / T) * (T : ℝ) ^ ρ := by
        rw [← Real.exp_nat_mul, ht]
        ring_nf

/-- A polynomial is eventually below an exponential with base `r > 1`. -/
theorem exists_mul_pow_le_pow (C : ℝ) (d : ℕ) {r : ℝ} (hr : 1 < r) :
    ∃ α : ℕ, 1 ≤ α ∧ C * (α : ℝ) ^ d ≤ r ^ α := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt d hr
  have hC : 0 < |C| + 1 := by positivity
  have hev := (hlim.eventually (gt_mem_nhds (inv_pos.mpr hC))).and (eventually_ge_atTop 1)
  obtain ⟨α, hα, hα1⟩ := hev.exists
  refine ⟨α, hα1, ?_⟩
  have hrα : 0 < r ^ α := pow_pos (by linarith) α
  rw [div_lt_iff₀ hrα] at hα
  have hpow : 0 ≤ (α : ℝ) ^ d := by positivity
  calc C * (α : ℝ) ^ d ≤ (|C| + 1) * (α : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hpow
    _ ≤ (|C| + 1) * ((|C| + 1)⁻¹ * r ^ α) := mul_le_mul_of_nonneg_left hα.le hC.le
    _ = r ^ α := by field_simp

/-- **The sparsification lemma, internal form.** -/
theorem exists_sparsification (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (N : ℕ) (φ : ClauseSet N), (∀ C ∈ φ, C.card ≤ k) →
      ∃ Ψ : Finset (ClauseSet N), (Ψ.card : ℝ) ≤ 2 ^ (ε * N) ∧
        (∀ ψ ∈ Ψ, (∀ C ∈ ψ, C.card ≤ k) ∧ (∀ v, ψ.occurrences v ≤ c) ∧
          ψ.solutions ⊆ φ.solutions) ∧
        φ.solutions ⊆ Ψ.biUnion solutions := by
  set K := max k 1 with hKdef
  have hK : 1 ≤ K := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the parameter `M` controls `exp (Λ / T)`
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / (ε * Real.log 2))
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM1 : 1 ≤ M := by exact_mod_cast hMpos
  have hMε : 1 / (M : ℝ) ≤ ε / 2 * Real.log 2 := by
    rw [div_le_iff₀ hMpos]
    have := (div_lt_iff₀ (by positivity : 0 < ε * Real.log 2)).mp hM
    nlinarith
  -- the parameter `α` controls `T ^ ρ`
  set r : ℝ := (2 : ℝ) ^ (ε / 2) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by positivity)
  set C₀ : ℝ := ((M * K * (2 * K) ^ (2 * K) : ℕ) : ℝ) ^ (K - 1)
  obtain ⟨α, hα, hαbound⟩ := exists_mul_pow_le_pow C₀ (2 * K * (K - 1)) hr1
  have hθ := one_le_threshold hK hα
  refine ⟨2 * ∑ j ∈ range K, threshold K α j, fun N φ hφ => ?_⟩
  have hφK : ∀ C ∈ φ, C.card ≤ K := fun C hC => (hφ C hC).trans (le_max_left _ _)
  obtain ⟨Ψ, hcard, hleaves, hcover⟩ := exists_leaves hK hα φ hφK
  refine ⟨Ψ, ?_, fun ψ hψ => ?_, fun x hx => ?_⟩
  · -- the number of leaves
    set X := base K α
    set Λ := N * (K * X ^ (2 * K))
    set ρ := (K - 1) * N / α
    set T := M * (K * X ^ (2 * K))
    have hX : 1 ≤ X := one_le_base hK hα
    have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))))
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have hTR1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hsum := sum_choose_le_exp_mul_pow Λ ρ T hT
    -- `exp (Λ / T) ≤ 2 ^ (ε N / 2)`
    have hexp : Real.exp (Λ / T) ≤ (2 : ℝ) ^ (ε / 2 * N) := by
      have hΛT : (Λ : ℝ) / T = N / M := by
        have hKX : (0 : ℝ) < (K * X ^ (2 * K) : ℕ) := by
          exact_mod_cast Nat.mul_pos (by omega) (pow_pos (by omega) _)
        simp only [Λ, T, Nat.cast_mul] at hKX ⊢
        field_simp
      rw [hΛT, Real.rpow_def_of_pos (by norm_num)]
      refine Real.exp_le_exp.mpr ?_
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      calc (N : ℝ) / M = N * (1 / M) := by ring
        _ ≤ N * (ε / 2 * Real.log 2) := mul_le_mul_of_nonneg_left hMε hN
        _ = Real.log 2 * (ε / 2 * N) := by ring
    -- `T ^ ρ ≤ 2 ^ (ε N / 2)`
    have hTK : (T : ℝ) ^ (K - 1) ≤ r ^ α := by
      have hTeq : (T : ℝ) ^ (K - 1) = C₀ * (α : ℝ) ^ (2 * K * (K - 1)) := by
        simp only [T, X, base, C₀, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        ring
      rw [hTeq]
      exact hαbound
    have hTρ : (T : ℝ) ^ ρ ≤ (2 : ℝ) ^ (ε / 2 * N) := by
      have hαρ : ρ * α ≤ (K - 1) * N := Nat.div_mul_le_self _ _
      have hpow : ((T : ℝ) ^ ρ) ^ α ≤ ((2 : ℝ) ^ (ε / 2 * N)) ^ α := by
        calc ((T : ℝ) ^ ρ) ^ α = (T : ℝ) ^ (ρ * α) := (pow_mul _ _ _).symm
          _ ≤ (T : ℝ) ^ ((K - 1) * N) := pow_le_pow_right₀ hTR1 hαρ
          _ = ((T : ℝ) ^ (K - 1)) ^ N := pow_mul _ _ _
          _ ≤ (r ^ α) ^ N := pow_le_pow_left₀ (by positivity) hTK N
          _ = ((2 : ℝ) ^ (ε / 2 * N)) ^ α := by
              rw [hr, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
                ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
              congr 1
              push_cast
              ring
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp hpow
    calc (Ψ.card : ℝ) ≤ ∑ j ∈ range (ρ + 1), (Λ.choose j : ℝ) := by exact_mod_cast hcard
      _ ≤ Real.exp (Λ / T) * (T : ℝ) ^ ρ := hsum
      _ ≤ (2 : ℝ) ^ (ε / 2 * N) * (2 : ℝ) ^ (ε / 2 * N) :=
          mul_le_mul hexp hTρ (by positivity) (by positivity)
      _ = 2 ^ (ε * N) := by
          rw [← Real.rpow_add (by norm_num)]
          ring_nf
  · obtain ⟨hsparse, hrefine, hsat⟩ := hleaves ψ hψ
    have hψK : ∀ C ∈ ψ, C.card ≤ K := fun C hC => by
      obtain ⟨D, hD, hCD⟩ := hrefine C hC
      exact (card_le_card hCD).trans (hφK D hD)
    refine ⟨fun C hC => ?_, occurrences_le_of_sparse hθ hsparse hψK, fun x hx => ?_⟩
    · obtain ⟨D, hD, hCD⟩ := hrefine C hC
      exact (card_le_card hCD).trans (hφ D hD)
    · exact mem_solutions.mpr (hsat x (mem_solutions.mp hx))
  · obtain ⟨ψ, hψ, hψx⟩ := hcover x (mem_solutions.mp hx)
    exact mem_biUnion.mpr ⟨ψ, hψ, mem_solutions.mpr hψx⟩

end Complexity.ClauseSet.Sparsify
